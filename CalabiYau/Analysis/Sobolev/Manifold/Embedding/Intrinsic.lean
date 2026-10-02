-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Embedding/Intrinsic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.ComponentNormBound
public import CalabiYau.Geometry.Riemannian.L2.Basic
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

open CalabiYau.Riemannian CalabiYau

set_option autoImplicit false

namespace Sobolev

noncomputable section

open MeasureTheory
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open scoped Manifold ContDiff

theorem sobolev_intrinsic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M)
    {p : Real} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        eLpNorm u
            (ENNReal.ofReal
              ((Module.finrank Real E : Real) * p /
                ((Module.finrank Real E : Real) - p)))
            (riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            (eLpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (gradFun (I := I) g u x)
                    (gradFun (I := I) g u x)))
                (ENNReal.ofReal p) (riemannianVolumeMeasure I M g)) := by
  classical
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  have hp_enn : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cs, hCs, hs⟩ :=
    Chart.sobolev_closed (I := I) (M := M) g hp_one hp_dim
  obtain ⟨Cr, hCr, hr⟩ :=
    EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      (I := I) (M := M) g hp_enn ENNReal.ofReal_ne_top
  refine ⟨Cs * Cr, mul_nonneg hCs hCr, ?_⟩
  intro u hu
  have hmem :
      Chart.MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u :=
    Equivalence.MemWkpChart_of_contMDiff (I := I) (M := M) hp_enn hu
  calc
    eLpNorm u
          (ENNReal.ofReal
            ((Module.finrank Real E : Real) * p /
              ((Module.finrank Real E : Real) - p)))
          (riemannianVolumeMeasure I M g) ≤
        ENNReal.ofReal Cs *
          Chart.wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u :=
      hs hu.continuous.measurable hmem
    _ ≤ ENNReal.ofReal Cs *
        (ENNReal.ofReal Cr *
          (eLpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (gradFun (I := I) g u x)
                  (gradFun (I := I) g u x)))
              (ENNReal.ofReal p) (riemannianVolumeMeasure I M g))) :=
      mul_le_mul_right (hr hu) _
    _ = ENNReal.ofReal (Cs * Cr) *
        (eLpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt
              (g.inner x
                (gradFun (I := I) g u x)
                (gradFun (I := I) g u x)))
            (ENNReal.ofReal p) (riemannianVolumeMeasure I M g)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hCs]

theorem sobolev_lpNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M)
    {p : Real} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        lpNorm u
            (ENNReal.ofReal
              ((Module.finrank Real E : Real) * p /
                ((Module.finrank Real E : Real) - p)))
            (riemannianVolumeMeasure I M g) ≤
          C *
            (lpNorm u (ENNReal.ofReal p) (riemannianVolumeMeasure I M g) +
              lpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (gradFun (I := I) g u x)
                    (gradFun (I := I) g u x)))
                (ENNReal.ofReal p) (riemannianVolumeMeasure I M g)) := by
  classical
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure I M g
  let _ : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let q := ENNReal.ofReal
    ((Module.finrank Real E : Real) * p /
      ((Module.finrank Real E : Real) - p))
  obtain ⟨C, hC, hSob⟩ := sobolev_intrinsic (I := I) (M := M) g hp_one hp_dim
  refine ⟨C, hC, ?_⟩
  intro u hu
  let gradNorm : M -> Real := fun x => Real.sqrt
    (g.inner x
      (gradFun (I := I) g u x)
      (gradFun (I := I) g u x))
  have hgrad_cont : Continuous gradNorm := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (gradG (I := I) g ⟨_, hu⟩) (gradG (I := I) g ⟨_, hu⟩)
    have hinner' : Continuous (fun x ↦
        g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)) :=
      hinner.congr (fun _ ↦ rfl)
    exact Real.continuous_sqrt.comp hinner'
  have hu_mem : MemLp u (ENNReal.ofReal p) μ := by
    exact hu.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrad_mem : MemLp gradNorm (ENNReal.ofReal p) μ := by
    exact hgrad_cont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright_ne :
      ENNReal.ofReal C *
          (eLpNorm u (ENNReal.ofReal p) μ +
            eLpNorm gradNorm (ENNReal.ofReal p) μ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.2
        ⟨hu_mem.eLpNorm_ne_top, hgrad_mem.eLpNorm_ne_top⟩)
  have hreal := ENNReal.toReal_mono hright_ne (hSob hu)
  simpa only [q, μ, gradNorm, ENNReal.toReal_mul, ENNReal.toReal_add,
      ENNReal.toReal_ofReal hC,
      ENNReal.toReal_add hu_mem.eLpNorm_ne_top hgrad_mem.eLpNorm_ne_top,
      toReal_eLpNorm hu.continuous.aestronglyMeasurable,
      toReal_eLpNorm hgrad_cont.aestronglyMeasurable] using hreal

theorem sobolev_two_lpNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        lpNorm u
            (ENNReal.ofReal
              ((Module.finrank Real E : Real) * 2 /
                ((Module.finrank Real E : Real) - 2)))
            (riemannianVolumeMeasure I M g) ≤
          C *
            (lpNorm u 2 (riemannianVolumeMeasure I M g) +
              lpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (gradFun (I := I) g u x)
                    (gradFun (I := I) g u x)))
                2 (riemannianVolumeMeasure I M g)) := by
  let _ : NeZero (Module.finrank Real E) := ⟨by
    intro hzero
    simp only [hzero, Nat.cast_zero] at hdim
    linarith⟩
  simpa only [ENNReal.ofReal_ofNat] using
    sobolev_lpNorm (I := I) (M := M) g (p := (2 : Real)) (by norm_num) hdim

theorem sq_sobolev_two_lpNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        lpNorm u
              (ENNReal.ofReal
                ((Module.finrank Real E : Real) * 2 /
                  ((Module.finrank Real E : Real) - 2)))
              (riemannianVolumeMeasure I M g) ^ 2 ≤
          2 * C ^ 2 *
            (lpNorm u 2 (riemannianVolumeMeasure I M g) ^ 2 +
              lpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (gradFun (I := I) g u x)
                    (gradFun (I := I) g u x)))
                2 (riemannianVolumeMeasure I M g) ^ 2) := by
  obtain ⟨C, hC, hSob⟩ := sobolev_two_lpNorm (I := I) (M := M) g hdim
  refine ⟨C, hC, ?_⟩
  intro u hu
  let A := lpNorm u
    (ENNReal.ofReal
      ((Module.finrank Real E : Real) * 2 /
        ((Module.finrank Real E : Real) - 2)))
    (riemannianVolumeMeasure I M g)
  let B := lpNorm u 2 (riemannianVolumeMeasure I M g)
  let D := lpNorm (fun x : M => Real.sqrt
      (g.inner x
        (gradFun (I := I) g u x)
        (gradFun (I := I) g u x)))
    2 (riemannianVolumeMeasure I M g)
  have hA : 0 ≤ A := lpNorm_nonneg
  have hB : 0 ≤ B := lpNorm_nonneg
  have hD : 0 ≤ D := lpNorm_nonneg
  have hmain : A ≤ C * (B + D) := hSob hu
  have hsquare : A ^ 2 ≤ (C * (B + D)) ^ 2 := by
    nlinarith
  have hadd : (B + D) ^ 2 ≤ 2 * (B ^ 2 + D ^ 2) := by
    nlinarith [sq_nonneg (B - D)]
  dsimp only [A, B, D] at hsquare ⊢
  calc
    _ ≤ (C * (B + D)) ^ 2 := hsquare
    _ = C ^ 2 * (B + D) ^ 2 := by ring
    _ ≤ C ^ 2 * (2 * (B ^ 2 + D ^ 2)) := by gcongr
    _ = 2 * C ^ 2 * (B ^ 2 + D ^ 2) := by ring

theorem sobolev_two_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank Real E : Real)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {u : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ u ->
        lpNorm u
              (ENNReal.ofReal
                ((Module.finrank Real E : Real) * 2 /
                  ((Module.finrank Real E : Real) - 2)))
              (riemannianVolumeMeasure I M g) ^ 2 ≤
          2 * C ^ 2 *
            ((∫ x, u x ^ 2 ∂(riemannianVolumeMeasure I M g)) +
              ∫ x, g.inner x
                  (gradFun (I := I) g u x)
                  (gradFun (I := I) g u x)
                ∂(riemannianVolumeMeasure I M g)) := by
  classical
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  obtain ⟨C, hC, hSob⟩ := sq_sobolev_two_lpNorm (I := I) (M := M) g hdim
  refine ⟨C, hC, ?_⟩
  intro u hu
  let μ := riemannianVolumeMeasure I M g
  let gradNorm : M -> Real := fun x => Real.sqrt
    (g.inner x
      (gradFun (I := I) g u x)
      (gradFun (I := I) g u x))
  have hu_l2 : lpNorm u 2 μ ^ 2 = ∫ x, u x ^ 2 ∂μ :=
    CalabiYau.L2.lpNorm_two_sq_eq_integral_sq
      hu.continuous.aestronglyMeasurable
  have hgrad_cont : Continuous gradNorm := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (gradG (I := I) g ⟨u, hu⟩) (gradG (I := I) g ⟨u, hu⟩)
    have hinner' : Continuous (fun x ↦
        g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)) :=
      hinner.congr (fun _ ↦ rfl)
    exact Real.continuous_sqrt.comp hinner'
  have hgrad_l2 : lpNorm gradNorm 2 μ ^ 2 =
      ∫ x, g.inner x
          (gradFun (I := I) g u x)
          (gradFun (I := I) g u x) ∂μ := by
    rw [CalabiYau.L2.lpNorm_two_sq_eq_integral_sq
      hgrad_cont.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all μ fun x => ?_)
    dsimp only [gradNorm]
    rw [Real.sq_sqrt]
    exact CalabiYau.metric_inner_self_nonneg
      (I := I) (M := M) g x _
  have hmain := hSob hu
  change lpNorm u
        (ENNReal.ofReal
          ((Module.finrank Real E : Real) * 2 /
            ((Module.finrank Real E : Real) - 2))) μ ^ 2 ≤ _
  simpa only [μ, gradNorm, hu_l2, hgrad_l2] using hmain

end

end Sobolev
