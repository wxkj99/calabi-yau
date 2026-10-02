module

public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Intrinsic
public import CalabiYau.Mathlib.MeasureTheory.Function.LpSpace.FiniteMeasureComparison

/-!
# The subcritical Sobolev inequality in complex dimension one

On a compact complex curve, the real dimension is two. The subcritical embedding with
`p = 4/3` gives the `L⁴` bound needed for the inhomogeneous Sobolev inequality with
`κ = 2`.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory
open CalabiYau.RiemannianVolume

namespace KahlerForm

section CanonicalBorel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin 1)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ω M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

local instance dimensionTwoMeasurableSpace : MeasurableSpace M := borel M
local instance dimensionTwoBorelSpace : BorelSpace M := ⟨rfl⟩

/-- The extracted subcritical embedding specialized to real dimension two. -/
private theorem dimensionTwo_subcriticalLpNorm
    (g : CalabiYau.SmoothRiemannianMetric
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : M → ℝ}, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
        lpNorm f (ENNReal.ofReal (4 : ℝ))
            (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) ≤
          C *
            (lpNorm f (ENNReal.ofReal (4 / 3 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) +
              lpNorm (fun x => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)))
                (ENNReal.ofReal (4 / 3 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g)) := by
  have hdimEq : Module.finrank ℝ (EuclideanSpace ℂ (Fin 1)) = 2 := by
    rw [finrank_real_of_complex]
    simp
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin 1))) :=
    ⟨by rw [hdimEq]; norm_num⟩
  have hdim : (4 / 3 : ℝ) < (Module.finrank ℝ (EuclideanSpace ℂ (Fin 1)) : ℝ) := by
    rw [hdimEq]
    norm_num
  obtain ⟨C, hC, hSob⟩ :=
    Sobolev.sobolev_lpNorm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) (M := M) g
      (p := (4 / 3 : ℝ)) (by norm_num) hdim
  refine ⟨C, hC, ?_⟩
  intro f hf
  have h := hSob hf
  rw [hdimEq] at h
  norm_num at h ⊢
  exact h

/-- Convert the subcritical estimate to an estimate with quadratic `L²` terms.
The proof is the finite-measure `L^{4/3}`-to-`L²` comparison applied to the function
and its Riemannian gradient norm. -/
private theorem subcriticalLpNorm_to_lpNormTwo
    (g : CalabiYau.SmoothRiemannianMetric
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M)
    (hsub : ∃ A : ℝ, 0 ≤ A ∧
      ∀ {f : M → ℝ}, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
        lpNorm f (ENNReal.ofReal (4 : ℝ))
            (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) ≤
          A *
            (lpNorm f (ENNReal.ofReal (4 / 3 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) +
              lpNorm (fun x => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)))
                (ENNReal.ofReal (4 / 3 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g))):
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {f : M → ℝ}, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
        lpNorm f (ENNReal.ofReal (4 : ℝ))
            (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) ≤
          B *
            (lpNorm f (ENNReal.ofReal (2 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) +
              lpNorm (fun x => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)))
                (ENNReal.ofReal (2 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g)) := by
  obtain ⟨A, hA, hsub⟩ := hsub
  let μ := riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g
  have : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) (M := M) g
  let D : ℝ := (μ Set.univ).toReal ^ (1 / 4 : ℝ)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hmem_of_continuous {u : M → ℝ} (hu : Continuous u) :
      MemLp u (ENNReal.ofReal (2 : ℝ)) μ := by
    have hmeas : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
    have hbound : ∃ C : ℝ, ∀ x : M, |u x| ≤ C := by
      by_cases hM : Nonempty M
      · have hrange : IsCompact (Set.range u) := isCompact_range hu
        obtain ⟨C₁, hC₁⟩ := hrange.bddAbove
        have hrange_neg : IsCompact (Set.range (-u)) := isCompact_range hu.neg
        obtain ⟨C₂, hC₂⟩ := hrange_neg.bddAbove
        refine ⟨max C₁ C₂, ?_⟩
        intro x
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have : -u x ≤ C₂ := hC₂ ⟨x, rfl⟩
          linarith [le_max_right C₁ C₂]
        · have : u x ≤ C₁ := hC₁ ⟨x, rfl⟩
          linarith [le_max_left C₁ C₂]
      · refine ⟨0, ?_⟩
        intro x
        exact (hM ⟨x⟩).elim
    obtain ⟨C, hC⟩ := hbound
    exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall fun x => hC x)
  refine ⟨A * D, mul_nonneg hA hD, ?_⟩
  intro f hf
  let gradNorm : M → ℝ := fun x => Real.sqrt
    (g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x))
  have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) (M := M) g
    (CalabiYau.Riemannian.gradG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g ⟨f, hf⟩)
    (CalabiYau.Riemannian.gradG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g ⟨f, hf⟩)
  have hinner' : Continuous (fun x => g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)) :=
    hinner.congr fun _ => rfl
  have hgradCont : Continuous gradNorm := by
    exact (Real.continuous_sqrt.comp hinner').congr fun x => rfl
  have hfun := MeasureTheory.lpNorm_fourThirds_le_measure_univ_rpow_mul_lpNorm_two
    (μ := μ) (f := f) hf.continuous.aestronglyMeasurable (hmem_of_continuous hf.continuous)
  have hgrad := MeasureTheory.lpNorm_fourThirds_le_measure_univ_rpow_mul_lpNorm_two
    (μ := μ) (f := gradNorm) hgradCont.aestronglyMeasurable
    (hmem_of_continuous hgradCont)
  have h := hsub hf
  change lpNorm f (ENNReal.ofReal (4 : ℝ)) μ ≤
    A * (lpNorm f (ENNReal.ofReal (4 / 3 : ℝ)) μ +
      lpNorm gradNorm (ENNReal.ofReal (4 / 3 : ℝ)) μ) at h
  change lpNorm f (ENNReal.ofReal (4 : ℝ)) μ ≤
    (A * D) * (lpNorm f (ENNReal.ofReal (2 : ℝ)) μ +
      lpNorm gradNorm (ENNReal.ofReal (2 : ℝ)) μ)
  calc
    lpNorm f (ENNReal.ofReal (4 : ℝ)) μ ≤
        A * (lpNorm f (ENNReal.ofReal (4 / 3 : ℝ)) μ +
          lpNorm gradNorm (ENNReal.ofReal (4 / 3 : ℝ)) μ) := h
    _ ≤ A * (D * lpNorm f (ENNReal.ofReal (2 : ℝ)) μ +
          D * lpNorm gradNorm (ENNReal.ofReal (2 : ℝ)) μ) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfun hgrad) hA
    _ = (A * D) * (lpNorm f (ENNReal.ofReal (2 : ℝ)) μ +
          lpNorm gradNorm (ENNReal.ofReal (2 : ℝ)) μ) := by ring

private theorem lpNorm_two_sq_eq_integral_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu : AEStronglyMeasurable u μ) :
    lpNorm u (ENNReal.ofReal (2 : ℝ)) μ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hu]
  norm_num
  have hnonneg : 0 ≤ ∫ x, u x ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg (u x)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
  norm_num

private theorem lpNorm_four_sq_eq_integral_norm_four
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu : AEStronglyMeasurable u μ) :
    lpNorm u (ENNReal.ofReal (4 : ℝ)) μ ^ 2 =
      (∫ x, ‖u x‖ ^ 4 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hu]
  norm_num
  have hnonneg : 0 ≤ ∫ x, |u x| ^ 4 ∂μ :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg _) _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
  norm_num

omit [T2Space M] [CompactSpace M] [SigmaCompactSpace M] in
private theorem riemannianGradNorm_continuous
    (g : CalabiYau.SmoothRiemannianMetric
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M)
    {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f) :
    Continuous (fun x => Real.sqrt
      (g.inner x
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x))) := by
  have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) (M := M) g
    (CalabiYau.Riemannian.gradG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g ⟨f, hf⟩)
    (CalabiYau.Riemannian.gradG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g ⟨f, hf⟩)
  have hinner' : Continuous (fun x => g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)) :=
    hinner.congr fun _ => rfl
  exact Real.continuous_sqrt.comp hinner'

set_option maxHeartbeats 1000000

/-- Convert a quadratic `L²` Riemannian Sobolev bound to the Kähler integral convention.
This is the Kähler-specific norm-to-integral and volume/gradient bridge. -/
private theorem lpNormTwo_to_sobolev
    (ω₀ : KahlerForm 1 M)
    (g : CalabiYau.SmoothRiemannianMetric
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M)
    (_hvol : ω₀.volume = riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g)
    (_hgrad : ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
      ∀ x, g.inner x
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) =
          2 * ω₀.gradNormSq f x)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧
      ∀ {f : M → ℝ}, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
        lpNorm f (ENNReal.ofReal (4 : ℝ))
            (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) ≤
          B *
            (lpNorm f (ENNReal.ofReal (2 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) +
              lpNorm (fun x => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)))
                (ENNReal.ofReal (2 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g))):
    ∃ C : ℝ, 0 ≤ C ∧ ω₀.SobolevInequality 2 C := by
  obtain ⟨B, hB, hbound⟩ := hbound
  let μ := riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g
  refine ⟨4 * B ^ 2, by positivity, ?_⟩
  intro f hf
  let gradNorm : M → ℝ := fun x => Real.sqrt
    (g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x))
  let X : ℝ := lpNorm f (ENNReal.ofReal (4 : ℝ)) μ
  let Y : ℝ := lpNorm f (ENNReal.ofReal (2 : ℝ)) μ
  let Z : ℝ := lpNorm gradNorm (ENNReal.ofReal (2 : ℝ)) μ
  have hgradCont : Continuous gradNorm := by
    simpa [gradNorm] using riemannianGradNorm_continuous g hf
  have hfAes : AEStronglyMeasurable f μ := hf.continuous.aestronglyMeasurable
  have hgradAes : AEStronglyMeasurable gradNorm μ :=
    hgradCont.aestronglyMeasurable
  have hXnonneg : 0 ≤ X := by simp [X, lpNorm_nonneg]
  have hYnonneg : 0 ≤ Y := by simp [Y, lpNorm_nonneg]
  have hZnonneg : 0 ≤ Z := by simp [Z, lpNorm_nonneg]
  have hlin : X ≤ B * (Y + Z) := by
    simpa [X, Y, Z, gradNorm, μ] using hbound hf
  have hsumSq : (Y + Z) ^ 2 ≤ 2 * (Y ^ 2 + Z ^ 2) := by
    nlinarith [sq_nonneg (Y - Z)]
  have hsq : X ^ 2 ≤ 2 * B ^ 2 * (Y ^ 2 + Z ^ 2) := by
    have hR : 0 ≤ B * (Y + Z) :=
      mul_nonneg hB (add_nonneg hYnonneg hZnonneg)
    calc
      X ^ 2 ≤ (B * (Y + Z)) ^ 2 := by
        simpa only [pow_two] using mul_le_mul hlin hlin hXnonneg hR
      _ = B ^ 2 * (Y + Z) ^ 2 := by ring
      _ ≤ B ^ 2 * (2 * (Y ^ 2 + Z ^ 2)) :=
        mul_le_mul_of_nonneg_left hsumSq (sq_nonneg B)
      _ = 2 * B ^ 2 * (Y ^ 2 + Z ^ 2) := by ring
  have hXid : X ^ 2 = (∫ x, |f x| ^ 4 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa [X, μ, Real.norm_eq_abs] using
      lpNorm_four_sq_eq_integral_norm_four (μ := μ) hfAes
  have hYid : Y ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    simpa [Y, μ, Real.norm_eq_abs, sq_abs] using
      lpNorm_two_sq_eq_integral_norm_sq (μ := μ) hfAes
  have hinner_nonneg (x : M) : 0 ≤ g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) := by
    rw [_hgrad f hf x]
    exact mul_nonneg (by norm_num) (ω₀.gradNormSq_nonneg f x)
  have hgradPoint (x : M) : ‖gradNorm x‖ ^ 2 = g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) := by
    change |Real.sqrt (g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x))| ^ 2 = _
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (hinner_nonneg x)
  have hZid : Z ^ 2 = ∫ x, g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
      (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) ∂μ := by
    calc
      Z ^ 2 = ∫ x, ‖gradNorm x‖ ^ 2 ∂μ := by
        simpa [Z, μ] using
          lpNorm_two_sq_eq_integral_norm_sq (μ := μ) hgradAes
      _ = ∫ x, g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
          (CalabiYau.Riemannian.gradFun
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hgradPoint x
  have hZenergy : Z ^ 2 = 2 * ∫ x, ω₀.gradNormSq f x ∂μ := by
    calc
      Z ^ 2 = ∫ x, g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
          (CalabiYau.Riemannian.gradFun
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) ∂μ := hZid
      _ = ∫ x, 2 * ω₀.gradNormSq f x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact _hgrad f hf x
      _ = 2 * ∫ x, ω₀.gradNormSq f x ∂μ := by rw [integral_const_mul]
  have hXvol : X ^ 2 = (∫ x, |f x| ^ 4 ∂ω₀.volume) ^ (1 / 2 : ℝ) := by
    simpa only [μ, ← _hvol] using hXid
  have hYvol : Y ^ 2 = ∫ x, f x ^ 2 ∂ω₀.volume := by
    simpa only [μ, ← _hvol] using hYid
  have hZvol : Z ^ 2 = 2 * ∫ x, ω₀.gradNormSq f x ∂ω₀.volume := by
    simpa only [μ, ← _hvol] using hZenergy
  have hFSqCont : Continuous (fun x => f x ^ 2) := by
    have hcont := hf.continuous.pow 2
    exact hcont.congr fun x => rfl
  have hFintR : Integrable (fun x => f x ^ 2) μ := by
    simpa only [μ] using CalabiYau.L2.integrable_of_continuous_compactSpace g hFSqCont
  have hGradSqCont : Continuous (fun x => gradNorm x ^ 2) := hgradCont.pow 2
  have hgradKahlerCont : Continuous (fun x => ω₀.gradNormSq f x) := by
    have hfun : (fun x => ω₀.gradNormSq f x) =
        fun x => (1 / 2 : ℝ) * gradNorm x ^ 2 := by
      funext x
      change ω₀.gradNormSq f x = (1 / 2 : ℝ) * Real.sqrt (g.inner x
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)) ^ 2
      rw [Real.sq_sqrt (hinner_nonneg x), _hgrad f hf x]
      ring
    rw [hfun]
    exact continuous_const.mul hGradSqCont
  have hGradIntR : Integrable (fun x => ω₀.gradNormSq f x) μ := by
    simpa only [μ] using CalabiYau.L2.integrable_of_continuous_compactSpace g
      hgradKahlerCont
  have hFint : Integrable (fun x => f x ^ 2) ω₀.volume := by
    rw [_hvol]
    exact hFintR
  have hGradInt : Integrable (fun x => ω₀.gradNormSq f x) ω₀.volume := by
    rw [_hvol]
    exact hGradIntR
  have hsumInt : ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume =
      (∫ x, ω₀.gradNormSq f x ∂ω₀.volume) +
        ∫ x, f x ^ 2 ∂ω₀.volume := integral_add hGradInt hFint
  have hFnonneg : 0 ≤ ∫ x, f x ^ 2 ∂ω₀.volume :=
    integral_nonneg fun x => sq_nonneg (f x)
  have henergy : X ^ 2 ≤ 4 * B ^ 2 *
      ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume := by
    calc
      X ^ 2 ≤ 2 * B ^ 2 * (Y ^ 2 + Z ^ 2) := hsq
      _ = 2 * B ^ 2 *
          ((∫ x, f x ^ 2 ∂ω₀.volume) +
            2 * ∫ x, ω₀.gradNormSq f x ∂ω₀.volume) := by rw [hYvol, hZvol]
      _ ≤ 4 * B ^ 2 *
          ((∫ x, ω₀.gradNormSq f x ∂ω₀.volume) +
            ∫ x, f x ^ 2 ∂ω₀.volume) := by nlinarith [sq_nonneg B, hFnonneg]
      _ = 4 * B ^ 2 *
          ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume := by rw [← hsumInt]
  have hsob : (∫ x, |f x| ^ 4 ∂ω₀.volume) ^ (1 / 2 : ℝ) ≤
      4 * B ^ 2 * ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume := by
    rw [← hXvol]
    exact henergy
  change (∫ x, |f x| ^ (2 * (2 : ℝ)) ∂ω₀.volume) ^ (2 : ℝ)⁻¹ ≤
    4 * B ^ 2 * ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume
  norm_num
  exact hsob

/-- Combine the finite-measure comparison with the Kähler norm-to-integral bridge. -/
private theorem subcriticalLpNorm_to_sobolev
    (ω₀ : KahlerForm 1 M)
    (g : CalabiYau.SmoothRiemannianMetric
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M)
    (_hvol : ω₀.volume = riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g)
    (_hgrad : ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
      ∀ x, g.inner x
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) =
          2 * ω₀.gradNormSq f x)
    (hsub : ∃ A : ℝ, 0 ≤ A ∧
      ∀ {f : M → ℝ}, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
        lpNorm f (ENNReal.ofReal (4 : ℝ))
            (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) ≤
          A *
            (lpNorm f (ENNReal.ofReal (4 / 3 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g) +
              lpNorm (fun x => Real.sqrt
                  (g.inner x
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
                    (CalabiYau.Riemannian.gradFun
                      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)))
                (ENNReal.ofReal (4 / 3 : ℝ))
                (riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g))):
    ∃ C : ℝ, 0 ≤ C ∧ ω₀.SobolevInequality 2 C := by
  obtain ⟨B, hB, hbound⟩ := subcriticalLpNorm_to_lpNormTwo g hsub
  exact lpNormTwo_to_sobolev ω₀ g _hvol _hgrad ⟨B, hB, hbound⟩

/-- Transfer the subcritical `W^{1,4/3}` embedding in real dimension two to the
quadratic-integral Sobolev inequality on a Kähler curve. -/
theorem sobolev_dimension_two
    (ω₀ : KahlerForm 1 M)
    (g : CalabiYau.SmoothRiemannianMetric
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M)
    (hvol : ω₀.volume = riemannianVolumeMeasure
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) M g)
    (hgrad : ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℝ) ∞ f →
      ∀ x, g.inner x
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x)
        (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin 1))) g f x) =
          2 * ω₀.gradNormSq f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ω₀.SobolevInequality 2 C := by
  exact subcriticalLpNorm_to_sobolev ω₀ g hvol hgrad
    (dimensionTwo_subcriticalLpNorm (M := M) g)

end CanonicalBorel

end KahlerForm
