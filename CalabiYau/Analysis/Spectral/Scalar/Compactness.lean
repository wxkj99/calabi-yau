-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Scalar/Compactness.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Spectral.Scalar.Resolvent
public import CalabiYau.Analysis.Spectral.Scalar.Spectrum
public import CalabiYau.Analysis.Elliptic.Operator.SmoothBridge
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.ComponentNormBound
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Sequences

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Analysis.Laplacian
open Sobolev
open Sobolev.Chart
open Sobolev.Equivalence
open Sobolev.EquivalenceReverse

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]
  [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_smoothScalar_le_norm_smoothScalar
    {g : SmoothRiemannianMetric I M} (s : SmoothScalar g) :
    eLpNorm s.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal ‖s‖ := by
  have h_norm_le : ‖smoothToLp (I := I) (M := M) g s‖ ≤ ‖s‖ := s.norm_smoothToLp_le
  have h_lp_norm_def :
      ‖smoothToLp (I := I) (M := M) g s‖ =
        (eLpNorm s.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [smoothToLp_apply]
    rw [Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp s.memLp_two)
  have h_finite : eLpNorm s.toFun 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ :=
    s.memLp_two.eLpNorm_ne_top
  have h_real : (eLpNorm s.toFun 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ ‖s‖ := by
    rw [← h_lp_norm_def]; exact h_norm_le
  have h_re : eLpNorm s.toFun 2
      (riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal (eLpNorm s.toFun 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal :=
    (ENNReal.ofReal_toReal h_finite).symm
  rw [h_re]
  exact ENNReal.ofReal_le_ofReal h_real

omit [NeZero (Module.finrank ℝ E)] in
private lemma sqrt_g_inner_grad_memLp_two
    {g : SmoothRiemannianMetric I M} (s : SmoothScalar g) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
      2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have h_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) :=
    Real.continuous_sqrt.comp (s.continuous_inner_grad s)
  exact h_cont.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_sqrt_g_inner_grad_le_norm_smoothScalar
    {g : SmoothRiemannianMetric I M} (s : SmoothScalar g) :
    eLpNorm (fun x : M => Real.sqrt
        (g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
      2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal ‖s‖ := by
  set f : M → ℝ := fun x : M => Real.sqrt
      (g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) with hf_def
  have hf_memLp : MemLp f 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    sqrt_g_inner_grad_memLp_two s
  set Fp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf_memLp.toLp f with hFp_def
  have h_norm_sq : ‖Fp‖ ^ 2 = ∫ x, f x * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h := real_inner_self_eq_norm_sq Fp
    rw [L2.inner_def (𝕜 := ℝ)] at h
    have hae : (fun a : M => @inner ℝ _ _ ((Fp : Lp ℝ 2 _) a) ((Fp : Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
        (fun a : M => f a * f a) := by
      have hae_coe : (Fp : Lp ℝ 2 _) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] f :=
        MemLp.coeFn_toLp hf_memLp
      filter_upwards [hae_coe] with a hae_a
      rw [hae_a]
      rfl
    rw [integral_congr_ae hae] at h
    exact h.symm
  have h_f_sq : ∀ x : M, f x * f x =
      g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    have hnn : 0 ≤ g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) :=
      SmoothRiemannianMetric_inner_self_nonneg g x _
    rw [hf_def]
    rw [show Real.sqrt _ * Real.sqrt _ = (Real.sqrt _) ^ 2 from (sq _).symm]
    exact Real.sq_sqrt hnn
  rw [show (fun x : M => f x * f x) = fun x => g.inner x
        ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) from
      funext h_f_sq] at h_norm_sq
  have h_decomp : ‖s‖ ^ 2 =
      (∫ x, s.toFun x * s.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    rw [s.norm_sq_eq_inner_self]
    rfl
  have h_l2_nn : 0 ≤ ∫ x, s.toFun x * s.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    s.integral_mul_self_nonneg
  have h_grad_le : (∫ x, g.inner x ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨s.toFun, s.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ ‖s‖ ^ 2 := by
    linarith
  have h_Fp_norm_sq_le : ‖Fp‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [h_norm_sq]; exact h_grad_le
  have h_Fp_norm_le : ‖Fp‖ ≤ ‖s‖ := by
    have h_rhs_nn : 0 ≤ ‖s‖ := norm_nonneg _
    exact abs_le_of_sq_le_sq' h_Fp_norm_sq_le h_rhs_nn |>.2
  have h_lp_norm_def :
      ‖Fp‖ =
        (eLpNorm f 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [hFp_def]
    rw [Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp hf_memLp)
  have h_finite : eLpNorm f 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ :=
    hf_memLp.eLpNorm_ne_top
  have h_real : (eLpNorm f 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ ‖s‖ := by
    rw [← h_lp_norm_def]; exact h_Fp_norm_le
  have h_re : eLpNorm f 2 (riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal (eLpNorm f 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal :=
    (ENNReal.ofReal_toReal h_finite).symm
  rw [h_re]
  exact ENNReal.ofReal_le_ofReal h_real

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_smooth_close_to_H1 (g : SmoothRiemannianMetric I M)
    (v : H1Compl g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : SmoothScalar g, ‖v - smoothToH1Compl (I := I) (M := M) g s‖ < δ := by
  have h_dense : DenseRange (smoothToH1Compl (I := I) (M := M) g) :=
    denseRange_smoothToH1Compl (I := I) (M := M) g
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall] at h_dense
  have hv_in : v ∈ closure (Set.range (smoothToH1Compl (I := I) (M := M) g)) :=
    h_dense v
  rw [Metric.mem_closure_iff] at hv_in
  obtain ⟨q, ⟨s, hs_eq⟩, hs_close⟩ := hv_in δ hδ
  refine ⟨s, ?_⟩
  rw [show smoothToH1Compl (I := I) (M := M) g s = q from hs_eq]
  rw [dist_eq_norm] at hs_close
  exact hs_close

theorem H1ComplToLp_isCompactOperator (g : SmoothRiemannianMetric I M) :
    IsCompactOperator (H1ComplToLp (I := I) (M := M) g) := by
  classical
  have h_iff := isCompactOperator_iff_isCompact_closure_image_closedBall
      (H1ComplToLp (I := I) (M := M) g : H1Compl g →ₗ[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) zero_lt_one
  refine h_iff.mpr ?_
  rw [isCompact_iff_isSeqCompact]
  set T : H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    H1ComplToLp (I := I) (M := M) g with hT_def
  intro y hy_in_closure
  have h_choose_z : ∀ n : ℕ, ∃ z ∈ T '' Metric.closedBall (0 : H1Compl g) 1,
      dist (y n) z < 1 / (n + 1 : ℝ) := by
    intro n
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hy_n := hy_in_closure n
    rw [Metric.mem_closure_iff] at hy_n
    exact hy_n _ h_pos
  choose z hz_mem hz_close using h_choose_z
  have h_choose_x : ∀ n : ℕ,
      ∃ x ∈ Metric.closedBall (0 : H1Compl g) 1, T x = z n := fun n => hz_mem n
  choose x hx_mem hx_eq using h_choose_x
  have h_choose_s : ∀ n : ℕ, ∃ s : SmoothScalar g,
      ‖x n - smoothToH1Compl (I := I) (M := M) g s‖ < 1 / (n + 1 : ℝ) := by
    intro n
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    exact exists_smooth_close_to_H1 (I := I) (M := M) g (x n) h_pos
  choose s hs_close using h_choose_s
  have h_xn_norm : ∀ n : ℕ, ‖x n‖ ≤ 1 := by
    intro n
    have hxn_mem : x n ∈ Metric.closedBall (0 : H1Compl g) 1 := hx_mem n
    rw [Metric.mem_closedBall, dist_zero_right] at hxn_mem
    exact hxn_mem
  have h_s_isometric : ∀ n : ℕ,
      ‖smoothToH1Compl (I := I) (M := M) g (s n)‖ = ‖s n‖ := by
    intro n
    rw [smoothToH1Compl_apply]
    exact UniformSpace.Completion.norm_coe (s n)
  have h_sn_norm_le_two : ∀ n : ℕ, ‖s n‖ ≤ 2 := by
    intro n
    have h_iso := h_s_isometric n
    have h_close : ‖x n - smoothToH1Compl (I := I) (M := M) g (s n)‖ ≤ 1 := by
      have h_lt : ‖x n - smoothToH1Compl (I := I) (M := M) g (s n)‖ < 1 / (n + 1) :=
        hs_close n
      have h_inv_le_one : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    have h_xn_le : ‖x n‖ ≤ 1 := h_xn_norm n
    have h_tri : ‖smoothToH1Compl (I := I) (M := M) g (s n)‖ ≤
        ‖x n‖ + ‖x n - smoothToH1Compl (I := I) (M := M) g (s n)‖ := by
      have h_id : smoothToH1Compl (I := I) (M := M) g (s n) =
          x n - (x n - smoothToH1Compl (I := I) (M := M) g (s n)) := by
        abel
      have h_norm_le : ‖x n - (x n - smoothToH1Compl (I := I) (M := M) g (s n))‖ ≤
          ‖x n‖ + ‖x n - smoothToH1Compl (I := I) (M := M) g (s n)‖ :=
        norm_sub_le (x n) (x n - smoothToH1Compl (I := I) (M := M) g (s n))
      have h_id' : ‖smoothToH1Compl (I := I) (M := M) g (s n)‖ =
          ‖x n - (x n - smoothToH1Compl (I := I) (M := M) g (s n))‖ := by
        rw [← h_id]
      rw [h_id']
      exact h_norm_le
    have h_smooth_le : ‖smoothToH1Compl (I := I) (M := M) g (s n)‖ ≤ 2 := by linarith
    rw [← h_iso]
    exact h_smooth_le
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_one_le_two : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform (E := E) (H := H)
      (I := I) (M := M) g (p := 2) h_one_le_two h_two_ne_top
  have h_wkp_bound : ∀ n : ℕ,
      wkpNormChart (I := I) (M := M) 1 2 (s n).toFun ≤
        ENNReal.ofReal (4 * C₀) := by
    intro n
    have h := hC₀_bound (s n).smooth
    have h_eq : (fun x : M => Real.sqrt
            (g.inner x
              (CalabiYau.Riemannian.gradFun
                (I := I) g (s n).toFun x)
              (CalabiYau.Riemannian.gradFun
                (I := I) g (s n).toFun x))) =
          (fun x : M => Real.sqrt
            (g.inner x ((gradG (I := I) g ⟨(s n).toFun, (s n).smooth⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((gradG (I := I) g ⟨(s n).toFun, (s n).smooth⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) := by
      funext x
      rfl
    rw [h_eq] at h
    have h_l2 := eLpNorm_smoothScalar_le_norm_smoothScalar (I := I) (M := M) (s n)
    have h_grad := eLpNorm_sqrt_g_inner_grad_le_norm_smoothScalar (I := I) (M := M) (s n)
    have h_sum_le :
        eLpNorm (s n).toFun 2
            (riemannianVolumeMeasure (I := I) (M := M) g) +
          eLpNorm (fun x : M => Real.sqrt
            (g.inner x ((gradG (I := I) g ⟨(s n).toFun, (s n).smooth⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((gradG (I := I) g ⟨(s n).toFun, (s n).smooth⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) 2
              (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal ‖s n‖ + ENNReal.ofReal ‖s n‖ :=
      add_le_add h_l2 h_grad
    have h_sn_le := h_sn_norm_le_two n
    have h_two_two : ENNReal.ofReal ‖s n‖ + ENNReal.ofReal ‖s n‖ ≤ ENNReal.ofReal (2 + 2) := by
      have h_sum : ENNReal.ofReal ‖s n‖ + ENNReal.ofReal ‖s n‖ =
          ENNReal.ofReal (‖s n‖ + ‖s n‖) :=
        (ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)).symm
      rw [h_sum]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h_chain := h_sum_le.trans h_two_two
    have h_step :
        wkpNormChart (I := I) (M := M) 1 2 (s n).toFun ≤
          ENNReal.ofReal C₀ * ENNReal.ofReal (2 + 2) := by
      refine h.trans ?_
      gcongr
    have h_mul : ENNReal.ofReal C₀ * ENNReal.ofReal (2 + 2) =
        ENNReal.ofReal (C₀ * (2 + 2)) :=
      (ENNReal.ofReal_mul hC₀_nn).symm
    rw [h_mul] at h_step
    have h_eq_4 : C₀ * (2 + 2) = 4 * C₀ := by ring
    rw [h_eq_4] at h_step
    exact h_step
  have h_sn_meas : ∀ n : ℕ, Measurable (s n).toFun := fun n =>
    (s n).smooth.continuous.measurable
  have h_one_le_ofReal_two : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h_sn_memWkp : ∀ n : ℕ, MemWkpChart
      (I := I) (M := M) 1 (ENNReal.ofReal 2) (s n).toFun := fun n =>
    MemWkpChart_of_contMDiff
      (I := I) (M := M) h_one_le_ofReal_two (s n).smooth
  have h_two_eq : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.ofReal_natCast]
    norm_num
  have h_wkp_bound' : ∀ n : ℕ,
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal 2) (s n).toFun ≤
        ENNReal.ofReal (4 * C₀) := by
    intro n
    rw [h_two_eq]
    exact h_wkp_bound n
  obtain ⟨φ, hφ_mono, u_lim, hu_lim_memLp_pou, hu_lim_tendsto_pou⟩ :=
    rellich_kondrachov_chart_seq
      (I := I) (M := M) g (p := 2) (by norm_num) h_sn_meas h_sn_memWkp h_wkp_bound'
  have h_pou_eq_g :
      CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) =
      riemannianVolumeMeasure (I := I) (M := M) g :=
    (riemannianVolumeMeasure_def (I := I) (M := M) g).symm
  rw [h_pou_eq_g] at hu_lim_memLp_pou
  rw [h_pou_eq_g] at hu_lim_tendsto_pou
  rw [h_two_eq] at hu_lim_memLp_pou
  rw [h_two_eq] at hu_lim_tendsto_pou
  set L : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hu_lim_memLp_pou.toLp u_lim with hL_def
  have h_smooth_tendsto :
      Tendsto (fun k => smoothToLp (I := I) (M := M) g (s (φ k))) atTop (𝓝 L) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (f := fun k => (s (φ k)).toFun)
        (f_ℒp := fun k => (s (φ k)).memLp_two)
        (f_lim := u_lim)
        (f_lim_ℒp := hu_lim_memLp_pou)).mpr hu_lim_tendsto_pou
    rw [hL_def]
    refine h.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
    exact smoothToLp_apply (I := I) (M := M) g (s (φ k))
  have h_y_tendsto : Tendsto (fun k => y (φ k)) atTop (𝓝 L) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun k : ℕ =>
        dist (y (φ k)) L) (fun k => dist_nonneg)
      (g := fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) +
              dist (smoothToLp (I := I) (M := M) g (s (φ k))) L)
      (fun k => ?_)
      ?_
    · have h_t1 : dist (y (φ k)) L ≤
          dist (y (φ k)) (z (φ k)) + dist (z (φ k)) L := dist_triangle _ _ _
      have h_t2 : dist (z (φ k)) L ≤
          dist (z (φ k)) (smoothToLp (I := I) (M := M) g (s (φ k))) +
            dist (smoothToLp (I := I) (M := M) g (s (φ k))) L :=
        dist_triangle _ _ _
      have h_yz : dist (y (φ k)) (z (φ k)) < 1 / ((φ k : ℝ) + 1) :=
        hz_close (φ k)
      have hT_s_eq : smoothToLp (I := I) (M := M) g (s (φ k)) =
          T (smoothToH1Compl (I := I) (M := M) g (s (φ k))) := by
        rw [hT_def]
        exact (H1ComplToLp_smoothToH1Compl (I := I) (M := M) g (s (φ k))).symm
      have h_zS_eq : z (φ k) - smoothToLp (I := I) (M := M) g (s (φ k)) =
          T (x (φ k) - smoothToH1Compl (I := I) (M := M) g (s (φ k))) := by
        rw [← hx_eq (φ k), hT_s_eq, ← T.map_sub]
      have h_zS_dist : dist (z (φ k)) (smoothToLp (I := I) (M := M) g (s (φ k))) =
          ‖T (x (φ k) - smoothToH1Compl (I := I) (M := M) g (s (φ k)))‖ := by
        rw [dist_eq_norm]
        rw [h_zS_eq]
      have h_zS_le : dist (z (φ k)) (smoothToLp (I := I) (M := M) g (s (φ k))) ≤
          ‖x (φ k) - smoothToH1Compl (I := I) (M := M) g (s (φ k))‖ := by
        rw [h_zS_dist]
        rw [hT_def]
        exact norm_H1ComplToLp_apply_le (I := I) (M := M) g _
      have h_xs_lt : ‖x (φ k) - smoothToH1Compl (I := I) (M := M) g (s (φ k))‖ <
          1 / ((φ k : ℝ) + 1) :=
        hs_close (φ k)
      have h_phi_ge : (k : ℝ) + 1 ≤ (φ k : ℝ) + 1 := by
        have h_phi_ge_k : k ≤ φ k := hφ_mono.le_apply
        exact_mod_cast Nat.add_le_add_right h_phi_ge_k 1
      have h_phi_pos : (0 : ℝ) < (φ k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (φ k : ℝ) := Nat.cast_nonneg _
        linarith
      have h_k_pos : (0 : ℝ) < (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith
      have h_inv_le : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le h_k_pos h_phi_ge
      calc
        dist (y (φ k)) L
            ≤ dist (y (φ k)) (z (φ k)) + dist (z (φ k)) L := h_t1
        _ ≤ dist (y (φ k)) (z (φ k)) +
              (dist (z (φ k)) (smoothToLp (I := I) (M := M) g (s (φ k))) +
                dist (smoothToLp (I := I) (M := M) g (s (φ k))) L) :=
              add_le_add le_rfl h_t2
        _ ≤ 1 / ((φ k : ℝ) + 1) + 1 / ((φ k : ℝ) + 1) +
              dist (smoothToLp (I := I) (M := M) g (s (φ k))) L := by
              have hzS_lt : dist (z (φ k)) (smoothToLp (I := I) (M := M) g (s (φ k))) <
                  1 / ((φ k : ℝ) + 1) := lt_of_le_of_lt h_zS_le h_xs_lt
              linarith [le_of_lt h_yz, le_of_lt hzS_lt]
        _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) +
              dist (smoothToLp (I := I) (M := M) g (s (φ k))) L := by
              linarith
        _ = 2 * (1 / ((k : ℝ) + 1)) +
              dist (smoothToLp (I := I) (M := M) g (s (φ k))) L := by ring
    · have h1 : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
        rw [show (0 : ℝ) = 2 * 0 by ring]
        exact (tendsto_const_nhds (x := (2 : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun k : ℕ =>
          dist (smoothToLp (I := I) (M := M) g (s (φ k))) L) atTop (𝓝 0) :=
        tendsto_iff_dist_tendsto_zero.mp h_smooth_tendsto
      rw [show (0 : ℝ) = 0 + 0 by ring]
      exact h1.add h2
  refine ⟨L, ?_, φ, hφ_mono, h_y_tendsto⟩
  · exact IsClosed.mem_of_tendsto isClosed_closure h_y_tendsto
      (Filter.Eventually.of_forall (fun k => hy_in_closure (φ k)))

theorem resolventL2_isCompactOperator (g : SmoothRiemannianMetric I M) :
    IsCompactOperator (resolventL2 (I := I) (M := M) g) := by
  have h_eq : (resolventL2 (I := I) (M := M) g : _ → _) =
      (H1ComplToLp (I := I) (M := M) g) ∘ (resolvent (I := I) (M := M) g) := by
    funext f
    rw [resolventL2_apply]
    rfl
  rw [show (resolventL2 (I := I) (M := M) g : _ → _) =
        (fun v => (H1ComplToLp (I := I) (M := M) g) v) ∘
          (fun f => (resolvent (I := I) (M := M) g) f) from h_eq]
  exact (H1ComplToLp_isCompactOperator (I := I) (M := M) g).comp_clm
    (resolvent (I := I) (M := M) g)

theorem resolventEigenspace_finiteDim_of_eigenvalue_ne_zero
    (g : SmoothRiemannianMetric I M)
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (resolventEigenspace (I := I) (M := M) g μ) :=
  resolventEigenspace_finiteDim (I := I) (M := M) g
    (resolventL2_isCompactOperator (I := I) (M := M) g) hμ

theorem resolventEigenspaces_iSup_orthogonal_eq_bot_on_closed
    (g : SmoothRiemannianMetric I M) :
    (⨆ μ : ℝ, resolventEigenspace (I := I) (M := M) g μ)ᗮ = ⊥ :=
  resolventEigenspaces_iSup_orthogonal_eq_bot (I := I) (M := M) g
    (resolventL2_isCompactOperator (I := I) (M := M) g)

theorem resolvent_eigenvalues_finite_above_on_closed
    (g : SmoothRiemannianMetric I M) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite { μ : ℝ |
      Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } :=
  resolvent_eigenvalues_finite_above (I := I) (M := M) g
    (resolventL2_isCompactOperator (I := I) (M := M) g) hε

end Laplacian
end CalabiYau

end
