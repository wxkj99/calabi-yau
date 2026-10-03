-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Embedding/Subcritical.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Basic
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.Compactness
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace EuclideanSubcritical

variable {d : ℕ}

local notation "EuN" => EuclideanSpace ℝ (Fin d)

private lemma eq_zero_off_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN} (hf_support : tsupport f ⊆ Ω)
    {x : EuN} (hx : x ∉ Ω) : f x = 0 := by
  have hx_notsupp : x ∉ tsupport f := fun h => hx (hf_support h)
  exact image_eq_zero_of_notMem_tsupport hx_notsupp

private lemma fderiv_eq_zero_off_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN}
    (hf_support : tsupport f ⊆ Ω)
    {x : EuN} (hx : x ∉ Ω) : fderiv ℝ f x = 0 := by
  have hx_notsupp : x ∉ tsupport f := fun h => hx (hf_support h)
  have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds hx_notsupp
  have hf_zero : f =ᶠ[𝓝 x] (fun _ : EuN => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem h_nhds ?_
    intro y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [Filter.EventuallyEq.fderiv_eq hf_zero]
  simp

private lemma eLpNorm_eq_eLpNorm_restrict_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN} (hΩ_meas : MeasurableSet Ω)
    (hf_support : tsupport f ⊆ Ω) (p : ℝ≥0∞) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict Ω) := by
  have h_eq : f = Ω.indicator f := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact eq_zero_off_of_tsupport_subset hf_support hx
  calc eLpNorm f p volume
      = eLpNorm (Ω.indicator f) p volume := by rw [← h_eq]
    _ = eLpNorm f p (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

private lemma eLpNorm_fderiv_eq_eLpNorm_fderiv_restrict_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN}
    (hΩ_meas : MeasurableSet Ω) (hf_support : tsupport f ⊆ Ω) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ f) p volume = eLpNorm (fderiv ℝ f) p (volume.restrict Ω) := by
  have h_eq : fderiv ℝ f = Ω.indicator (fderiv ℝ f) := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact fderiv_eq_zero_off_of_tsupport_subset hf_support hx
  calc eLpNorm (fderiv ℝ f) p volume
      = eLpNorm (Ω.indicator (fderiv ℝ f)) p volume := by rw [← h_eq]
    _ = eLpNorm (fderiv ℝ f) p (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (p := p) (f := fderiv ℝ f) (s := Ω) hΩ_meas

private lemma classical_partial_ae_eq_chosenWeakPartial_of_smooth
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω) (i : Fin d) :
    (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω := by
  have hf_mem : Sobolev.Euclidean.MemWkp (d := d) 1 p f Ω :=
    Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := d) hΩ_open hf_smooth hf_compact hf_support hp_one 1
  have hf_W1p : Sobolev.Euclidean.MemW1p (d := d) p f Ω :=
    Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := d) i
        (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω :=
    Sobolev.Euclidean.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f) (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := d) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω) f Ω :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_local : LocallyIntegrable
      (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
      (volume.restrict Ω) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      hf_W1p i).locallyIntegrable hp_one
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_local h_chosen_local

private lemma norm_fderiv_le_sum_norm_partials
    (f : EuN → ℝ) (x : EuN) :
    ‖fderiv ℝ f x‖ ≤ ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ := by
  classical
  set v : EuN := (InnerProductSpace.toDual ℝ EuN).symm (fderiv ℝ f x) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuN) v = fderiv ℝ f x := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ f x‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2 (fun i : Fin d => (fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1))) i := by simp
  have h_v_sum :
      v = ∑ i : Fin d, EuclideanSpace.single i ((fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
    ext j
    rw [h_v_eq_components]
    simp [Finset.sum_apply]
  rw [h_fderiv_norm_eq_v, h_v_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

private lemma eLpNorm_fderiv_le_sum_eLpNorm_partials
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {μ : Measure EuN}
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    eLpNorm (fderiv ℝ f) p μ ≤
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p μ := by
  classical
  have h_aesm_comp : ∀ i : Fin d,
      AEStronglyMeasurable
        (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ x : EuN,
      ‖fderiv ℝ f x‖ ≤ ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ :=
    fun x => norm_fderiv_le_sum_norm_partials (d := d) f x
  have h_aesm_fderiv : AEStronglyMeasurable (fderiv ℝ f) μ :=
    (hf_smooth.continuous_fderiv (by simp)).aestronglyMeasurable
  have h_step1 : eLpNorm (fderiv ℝ f) p μ
      = eLpNorm (fun x => ‖fderiv ℝ f x‖) p μ :=
    (eLpNorm_norm _ h_aesm_fderiv).symm
  rw [h_step1]
  have h_step2 : eLpNorm (fun x : EuN => ‖fderiv ℝ f x‖) p μ ≤
      eLpNorm
        (fun x : EuN => ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) p μ := by
    apply eLpNorm_mono_real h_aesm_fderiv.norm
    intro x
    have h := h_pt x
    have h_norm : ‖‖fderiv ℝ f x‖‖ = ‖fderiv ℝ f x‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact h
  refine h_step2.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := p)
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => fun x : EuN => ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖)
    hp_one
  have h_lhs_eq :
      (fun x : EuN => ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin d, fun x : EuN => ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ := by
    funext x
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm _ (h_aesm_comp i)]

private lemma eLpNorm_classical_partial_eq_chosen
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω) (i : Fin d) :
    eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p (volume.restrict Ω)
      = eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
          p (volume.restrict Ω) :=
  eLpNorm_congr_ae
    (classical_partial_ae_eq_chosenWeakPartial_of_smooth
      (d := d) hp_one hΩ_open hf_smooth hf_compact hf_support i)
section

variable [NeZero d]


private lemma eLpNorm_fderiv_smooth_le_d_mul_wkpNorm
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω) :
    eLpNorm (fderiv ℝ f) p (volume.restrict Ω) ≤
      (d : ℝ≥0∞) *
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f
          Ω := by
  classical
  have h_grad_le := eLpNorm_fderiv_le_sum_eLpNorm_partials (d := d) hp_one
    (μ := volume.restrict Ω) hf_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin d,
      eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p (volume.restrict Ω)
        = eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
            p (volume.restrict Ω) := fun i =>
    eLpNorm_classical_partial_eq_chosen (d := d) hp_one hΩ_open hf_smooth hf_compact hf_support i
  have h_step1 :
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p (volume.restrict Ω)
        = ∑ i : Fin d,
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
            p (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin d,
            eLpNorm
              (Sobolev.Euclidean.iterWeakPartial
                (d := d) p j β f Ω)
              p (volume.restrict Ω) :=
    Sobolev.Euclidean.wkpNorm_eq_sum 1 p f Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin d,
          eLpNorm
            (Sobolev.Euclidean.iterWeakPartial
              (d := d) p 1 β f Ω) p (volume.restrict Ω)) =
        ∑ i : Fin d,
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
            p (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin d,
        eLpNorm
          (Sobolev.Euclidean.iterWeakPartial
            (d := d) p 1 β f Ω) p (volume.restrict Ω) =
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero p (β 0) f Ω)
            p (volume.restrict Ω) := by
      intro β
      have hit :
          Sobolev.Euclidean.iterWeakPartial
              (d := d) p 1 β f Ω =
            Sobolev.Euclidean.chosenWeakPartialOrZero p (β 0) f Ω := by
        rw [Sobolev.Euclidean.iterWeakPartial_succ]
        simp [Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin d) ≃ Fin d :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero p (β 0) f Ω)
          p (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
          p (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin d,
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
            p (volume.restrict Ω)) ≤
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f
          Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < d := NeZero.pos d
  have hd_one_le : (1 : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by exact_mod_cast hd_pos
  conv_lhs => rw [show Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := d) 1 p f Ω = 1 *
    Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f Ω from
    (one_mul _).symm]
  gcongr

private lemma sobolev_smooth_compactSupport_in_Ω
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {φ : EuN → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ Ω) :
    eLpNorm φ
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict Ω) ≤
      ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) *
        eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) (volume.restrict Ω) := by
  have h_lhs_eq :
      eLpNorm φ
          (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume =
        eLpNorm φ
          (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict Ω) :=
    eLpNorm_eq_eLpNorm_restrict_of_tsupport_subset (d := d)
      hΩ_open.measurableSet hφ_support _
  have h_rhs_eq :
      eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) volume =
        eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) (volume.restrict Ω) :=
    eLpNorm_fderiv_eq_eLpNorm_fderiv_restrict_of_tsupport_subset (d := d)
      hΩ_open.measurableSet hφ_support _
  have h_smooth_sob := Sobolev.Euclidean.sobolev_smooth (d := d) hp_one hp_dim
    (hφ_smooth.of_le (by norm_cast)) hφ_compact
  rw [← h_lhs_eq, ← h_rhs_eq]
  exact h_smooth_sob

theorem eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ}
    (hf : Sobolev.Euclidean.MemWkp (d := d)
      1 (ENNReal.ofReal p) f Ω)
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω) :
    eLpNorm f
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict Ω) ≤
      ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) *
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d)
          1 (ENNReal.ofReal p) f Ω := by
  classical
  set p_enn : ℝ≥0∞ := ENNReal.ofReal p with hp_enn_def
  set p_star_real : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_star_real_def
  set p_star : ℝ≥0∞ := ENNReal.ofReal p_star_real with hp_star_def
  have hp_pos : 0 < p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : p_enn ≠ ⊤ := by rw [hp_enn_def]; exact ENNReal.ofReal_ne_top
  have hp_star_pos : 0 < p_star_real := by
    rw [hp_star_real_def]
    apply div_pos
    · exact mul_pos (by exact_mod_cast (NeZero.pos d)) hp_pos
    · linarith
  have hp_enn_ne_zero : p_enn ≠ 0 := by
    rw [hp_enn_def]; exact ENNReal.ofReal_ne_zero_iff.mpr hp_pos
  have h_pick : ∀ n : ℕ, ∃ φ : EuN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ x) Ω ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have h_eps_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      apply div_pos one_pos
      exact_mod_cast Nat.succ_pos n
    exact Sobolev.Euclidean.MemWkp.exists_smooth_compactSupport_approx
      (d := d) hΩ_open 1 p_enn hp_enn_one hp_enn_top hf hf_compact hf_support
      (1 / (n + 1 : ℝ)) h_eps_pos
  set φ : ℕ → EuN → ℝ := fun n => (h_pick n).choose with hφ_def
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := fun n => (h_pick n).choose_spec.1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := fun n => (h_pick n).choose_spec.2.1
  have hφ_support : ∀ n, tsupport (φ n) ⊆ Ω := fun n => (h_pick n).choose_spec.2.2.1
  have hφ_close : ∀ n,
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ n x) Ω ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) :=
    fun n => (h_pick n).choose_spec.2.2.2
  have h_smooth_sob : ∀ n,
      eLpNorm (φ n) p_star (volume.restrict Ω) ≤
        ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) *
          eLpNorm (fderiv ℝ (φ n)) p_enn (volume.restrict Ω) := fun n =>
    sobolev_smooth_compactSupport_in_Ω (d := d) hp_one hp_dim hΩ_open
      (hφ_smooth n) (hφ_compact n) (hφ_support n)
  have h_grad_bound : ∀ n,
      eLpNorm (fderiv ℝ (φ n)) p_enn (volume.restrict Ω) ≤
        (d : ℝ≥0∞) *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (φ n) Ω :=
    fun n => eLpNorm_fderiv_smooth_le_d_mul_wkpNorm
      (d := d) (p := p_enn) hp_enn_one hΩ_open (hφ_smooth n) (hφ_compact n) (hφ_support n)
  have h_φn_mem : ∀ n,
      Sobolev.Euclidean.MemWkp (d := d)
        1 p_enn (φ n) Ω := fun n =>
    Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := d) hΩ_open (hφ_smooth n) (hφ_compact n) (hφ_support n) hp_enn_one 1
  have h_diff_mem : ∀ n,
      Sobolev.Euclidean.MemWkp (d := d)
        1 p_enn (fun x => f x - φ n x) Ω := fun n =>
    Sobolev.Euclidean.MemWkp.sub
      (d := d) hp_enn_one hΩ_open hf (h_φn_mem n)
  have h_wkp_φn_le : ∀ n,
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn (φ n)
        Ω ≤
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn f Ω +
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ n x) Ω := by
    intro n
    have h_φn_decomp : (φ n) = (fun x => (φ n x - f x) + f x) := by funext x; ring
    rw [h_φn_decomp]
    have h_v_mem :
        Sobolev.Euclidean.MemWkp (d := d)
          1 p_enn (fun x => φ n x - f x) Ω :=
      Sobolev.Euclidean.MemWkp.sub
        (d := d) hp_enn_one hΩ_open (h_φn_mem n) hf
    have h_tri := Sobolev.Euclidean.wkpNorm_add_le
      (d := d) hp_enn_one hΩ_open h_v_mem hf
    refine h_tri.trans ?_
    have h_neg_eq :
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
            (fun x => φ n x - f x) Ω =
          Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
            (fun x => f x - φ n x) Ω := by
      have h_eq : (fun x : EuN => φ n x - f x) = (fun x : EuN => -(f x - φ n x)) := by
        funext x; ring
      rw [h_eq]
      have h_smul := Sobolev.Euclidean.wkpNorm_const_smul
        (d := d) hp_enn_one hΩ_open (h_diff_mem n) (-1)
      have h_smul_eq :
          (fun x : EuN => (-1 : ℝ) * (f x - φ n x)) = (fun x : EuN => -(f x - φ n x)) := by
        funext x; ring
      rw [h_smul_eq] at h_smul
      rw [h_smul]
      simp
    rw [h_neg_eq, add_comm]
    have h_simplify : (fun x : EuN => f x - (φ n x - f x + f x)) = (fun x => f x - φ n x) := by
      funext x; ring
    rw [h_simplify]
  have h_eLpNorm_diff_le_wkp : ∀ n,
      eLpNorm (fun x => f x - φ n x) p_enn (volume.restrict Ω) ≤
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ n x) Ω :=
    fun n =>
      Sobolev.Chart.Euclidean.wkpNorm_zero_le_wkpNorm
        (d := d) (k := 1) (p := p_enn)
        (u := fun x => f x - φ n x) (Ω := Ω)
  have h_decay_to_zero : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)))
      atTop (nhds 0) := by
    have hReal : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
        have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact h2.atTop_add tendsto_const_nhds
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hReal
  have h_eLpNorm_diff_to_zero : Tendsto (fun n => eLpNorm
      (fun x => f x - φ n x) p_enn (volume.restrict Ω)) atTop (nhds 0) := by
    have h_total_le : ∀ n,
        eLpNorm (fun x => f x - φ n x) p_enn (volume.restrict Ω) ≤
          ENNReal.ofReal (1 / (n + 1 : ℝ)) := fun n =>
      (h_eLpNorm_diff_le_wkp n).trans (hφ_close n)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_decay_to_zero
      (Filter.Eventually.of_forall (fun _ => zero_le))
      (Filter.Eventually.of_forall h_total_le)
  have hf_aesm : AEStronglyMeasurable f (volume.restrict Ω) := hf.memLp.aestronglyMeasurable
  have hφ_aesm : ∀ n, AEStronglyMeasurable (φ n) (volume.restrict Ω) :=
    fun n => (hφ_smooth n).continuous.aestronglyMeasurable
  have h_tim : TendstoInMeasure (volume.restrict Ω) φ atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm hp_enn_ne_zero ?_
    have h_neg_eq : ∀ n,
        eLpNorm (fun x => φ n x - f x) p_enn (volume.restrict Ω) =
          eLpNorm (fun x => f x - φ n x) p_enn (volume.restrict Ω) := by
      intro n
      have h_eq : (fun x : EuN => φ n x - f x) = (fun x : EuN => -(f x - φ n x)) := by
        funext x; ring
      rw [h_eq]
      have h_neg_apply : (fun x : EuN => -(f x - φ n x)) = -(fun x : EuN => f x - φ n x) := by
        funext x; rfl
      rw [h_neg_apply, eLpNorm_neg]
    refine (Filter.tendsto_congr h_neg_eq).mpr h_eLpNorm_diff_to_zero
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := h_tim.exists_seq_tendsto_ae
  have h_aesm_subseq : ∀ n, AEStronglyMeasurable (φ (σ n)) (volume.restrict Ω) :=
    fun n => hφ_aesm (σ n)
  have h_fatou : eLpNorm f p_star (volume.restrict Ω) ≤
      atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star (volume.restrict Ω)) :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm h_aesm_subseq f hf_aesm hσ_ae
  set C : ℝ≥0∞ := ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) with hC_def
  set N : ℝ≥0∞ := Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := d) 1 p_enn f Ω with hN_def
  have h_per_n : ∀ n,
      eLpNorm (φ (σ n)) p_star (volume.restrict Ω) ≤
        C *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (φ (σ n)) Ω := by
    intro n
    have h1 := h_smooth_sob (σ n)
    have h2 := h_grad_bound (σ n)
    calc eLpNorm (φ (σ n)) p_star (volume.restrict Ω)
        ≤ ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) *
            eLpNorm (fderiv ℝ (φ (σ n))) p_enn (volume.restrict Ω) := h1
      _ ≤ ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) *
            ((d : ℝ≥0∞) *
              Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := d) 1 p_enn (φ (σ n)) Ω) := by gcongr
      _ = C *
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := d) 1 p_enn (φ (σ n)) Ω := by rw [hC_def]; ring
  have h_wkp_subseq : ∀ n,
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (φ (σ n)) Ω ≤ N +
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω :=
    fun n => h_wkp_φn_le (σ n)
  have h_per_n_v2 : ∀ n,
      eLpNorm (φ (σ n)) p_star (volume.restrict Ω) ≤
        C * (N +
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) := fun n =>
    (h_per_n n).trans (by gcongr; exact h_wkp_subseq n)
  have h_liminf_le_C_lim :
      atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star (volume.restrict Ω))
      ≤ atTop.liminf (fun n => C * (N +
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω)) := by
    refine Filter.liminf_le_liminf (Filter.Eventually.of_forall h_per_n_v2) ?_ ?_
    · exact isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall (fun _ => zero_le))
    · exact isCoboundedUnder_ge_of_eventually_le atTop
        (Filter.Eventually.of_forall (fun _ => le_top))
  have h_wkp_diff_decay : Tendsto (fun n =>
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ n x) Ω) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_decay_to_zero
      (Filter.Eventually.of_forall (fun _ => zero_le))
      (Filter.Eventually.of_forall hφ_close)
  have h_wkp_diff_subseq_decay : Tendsto (fun n =>
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) atTop (nhds 0) :=
    h_wkp_diff_decay.comp hσ_mono.tendsto_atTop
  have hC_ne_top : C ≠ ⊤ := by
    rw [hC_def]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  have h_C_diff_decay : Tendsto (fun n => C *
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) atTop (nhds 0) := by
    simpa using
      (ENNReal.Tendsto.const_mul h_wkp_diff_subseq_decay (Or.inr hC_ne_top))
  have h_alg : (fun n => C * (N +
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω)) =
      (fun n => C * N + C *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) := by
    funext n
    rw [mul_add]
  rw [h_alg] at h_liminf_le_C_lim
  have h_liminf_const_add :
      atTop.liminf (fun n => C * N + C *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω)
        = C * N := by
    rw [show (fun n => C * N + C *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) =
      (fun _ => C * N) + (fun n => C *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) by rfl]
    rw [ENNReal.liminf_add_of_right_tendsto_zero h_C_diff_decay]
    simp
  rw [h_liminf_const_add] at h_liminf_le_C_lim
  exact h_fatou.trans h_liminf_le_C_lim

end

end EuclideanSubcritical

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma tsupport_pou_mul_subset_tsupport_pou_subcrit
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport (ρ α : M → ℝ) := by
  have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by
    funext x; rfl
  rw [h_eq]
  exact tsupport_smul_subset_left
    (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma measurable_pou_mul_subcrit
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    {u : M → ℝ} (hu : Measurable u) :
    Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) := by
  have hcont : Continuous (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x) :=
    (ρ α).contMDiff.continuous
  exact hcont.measurable.mul hu

private lemma toEuclidean_extChartAt_tsupport_pou_compact_subset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] (α : M) :
    IsCompact (toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)))) ∧
      toEuclidean ''
          ((extChartAt I α) ''
            (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ))) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
  set Tα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_source : Tα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hTα_ext_source : Tα ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]; exact hTα_chart_source hx
  have hcont_ext : ContinuousOn (extChartAt I α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_source
  have hImage_ext_compact : IsCompact ((extChartAt I α) '' Tα) :=
    hTα_compact.image_of_continuousOn hcont_ext
  have hImage_eucl_compact : IsCompact (toEuclidean '' ((extChartAt I α) '' Tα)) :=
    hImage_ext_compact.image (toEuclidean (E := E)).continuous
  refine ⟨hImage_eucl_compact, ?_⟩
  rintro y ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
  refine ⟨z, ?_, hzy⟩
  rw [← hxz]
  exact (extChartAt I α).map_source (hTα_ext_source hx_support)

private lemma tsupport_chartPushedRaw_pou_mul_subset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := toEuclidean ''
    ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ))) with hK_def
  have hK_compact : IsCompact K :=
    (toEuclidean_extChartAt_tsupport_pou_compact_subset (I := I) (M := M) α).1
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_support_sub : Function.support (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    classical
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
      set z : M := (extChartAt I α).symm
        ((toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))).symm y) with hz_def
      have hρ_z : (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) z = 0 := by
        by_contra hρne
        apply hyK
        have hz_support : z ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _ (Function.mem_support.mpr hρne)
        refine ⟨(toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))).symm y,
          ⟨z, hz_support, ?_⟩, ?_⟩
        · rw [hz_def]
          rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
          exact (extChartAt I α).right_inv hy_target
        · exact (toEuclidean (E := E)).apply_symm_apply y
      change (((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) * u z = 0
      rw [hρ_z]; ring
    · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_support_sub

private lemma hasCompactSupport_chartPushedRaw_pou_mul
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] (α : M) (u : M → ℝ) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) := by
  have hK_compact : IsCompact (toEuclidean '' ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))) :=
    (toEuclidean_extChartAt_tsupport_pou_compact_subset (I := I) (M := M) α).1
  exact hK_compact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartPushedRaw_pou_mul_subset (I := I) (M := M) α u)

private lemma tsupport_chartPushedRaw_pou_mul_subset_target
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (tsupport_chartPushedRaw_pou_mul_subset (I := I) (M := M) α u).trans
    (toEuclidean_extChartAt_tsupport_pou_compact_subset (I := I) (M := M) α).2

private lemma memWkp_chartPushedRaw_pou_mul_of_memWkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) 1 p u) (α : M) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E)
      1 p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_chart_pushed := hu α
  have h_ae : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) :=
    chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
  have hopen := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one hopen h_ae).mp h_chart_pushed

private lemma wkpNorm_chartPushedRaw_pou_mul_eq_chartPushed
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (u : M → ℝ) (α : M) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E)
        1 p
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E)
        1 p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) := by
  let _ := g
  refine Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α) ?_
  exact (chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u).symm

private theorem perChart_eLpNorm_pStar_le
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank ℝ E : ℝ)) (α : M) :
    ∃ K_α : ℝ≥0∞, K_α ≠ ⊤ ∧
      ∀ {u : M → ℝ}, Measurable u →
        MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u →
        eLpNorm
            (fun x : M =>
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x)
            (ENNReal.ofReal
              ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
          K_α * wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  have hd_pos : 0 < d := NeZero.pos d
  set p_enn : ℝ≥0∞ := ENNReal.ofReal p with hp_enn_def
  set p_star_real : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_star_real_def
  set p_star : ℝ≥0∞ := ENNReal.ofReal p_star_real with hp_star_def
  have hp_pos : 0 < p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : p_enn ≠ ⊤ := by rw [hp_enn_def]; exact ENNReal.ofReal_ne_top
  have hp_star_pos : 0 < p_star_real := by
    rw [hp_star_real_def]
    apply div_pos
    · exact mul_pos (by exact_mod_cast hd_pos) hp_pos
    · linarith
  have hp_star_ge_p : p ≤ p_star_real := by
    rw [hp_star_real_def, le_div_iff₀ (by linarith : 0 < (d : ℝ) - p)]
    nlinarith [hp_pos]
  have hp_star_real_one : 1 ≤ p_star_real := le_trans hp_one hp_star_ge_p
  have hp_star_one : (1 : ℝ≥0∞) ≤ p_star := by
    rw [hp_star_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_star_real_one
  have hp_star_top : p_star ≠ ⊤ := by rw [hp_star_def]; exact ENNReal.ofReal_ne_top
  set ρ := CalabiYau.RiemannianVolume.chartAtlasPOU I M with hρ_def
  set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  obtain ⟨C_α, hC_α_pos, hbridge⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_star_one hp_star_top
  set C_d : ℝ≥0∞ := ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) with hC_d_def
  have hC_d_ne_top : C_d ≠ ⊤ := by
    rw [hC_d_def]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  set K_α : ℝ≥0∞ := ENNReal.ofReal C_α * C_d with hK_α_def
  have hK_α_ne_top : K_α ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC_d_ne_top
  refine ⟨K_α, hK_α_ne_top, ?_⟩
  intro u hu_meas hu
  have h_support : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ Kα :=
    tsupport_pou_mul_subset_tsupport_pou_subcrit (I := I) (M := M) ρ α u
  have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
    measurable_pou_mul_subcrit (I := I) (M := M) ρ α hu_meas
  have h_bridge :
      eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p_star
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_α *
            eLpNorm (chartPushedRaw I α (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
              p_star
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
    hbridge h_meas h_support
  set f := chartPushedRaw (I := I) (M := M) α
    (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hf_memWkp :
      Sobolev.Euclidean.MemWkp (d := d)
        1 p_enn f (chartTargetEuclid (I := I) (M := M) α) :=
    memWkp_chartPushedRaw_pou_mul_of_memWkpChart (I := I) (M := M) hp_enn_one hu α
  have hf_compact : HasCompactSupport f :=
    hasCompactSupport_chartPushedRaw_pou_mul (I := I) (M := M) α u
  have hf_support : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α :=
    tsupport_chartPushedRaw_pou_mul_subset_target (I := I) (M := M) α u
  have h_eucl_sob :
      eLpNorm f p_star
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
        C_d *
          Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d)
            1 p_enn f (chartTargetEuclid (I := I) (M := M) α) := by
    have h_main :=
      EuclideanSubcritical.eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp
        (d := d) hp_one hp_dim
        (Ω := chartTargetEuclid (I := I) (M := M) α)
        (chartTargetEuclid_isOpen (I := I) (M := M) α)
        hf_memWkp hf_compact hf_support
    convert h_main using 1
  have h_wkp_eq :
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn f
          (chartTargetEuclid (I := I) (M := M) α) =
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_chartPushedRaw_pou_mul_eq_chartPushed (I := I) (M := M) g hp_enn_one u α
  rw [h_wkp_eq] at h_eucl_sob
  have h_wkp_chart_le :
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        wkpNormChart (I := I) (M := M) 1 p_enn u := by
    unfold wkpNormChart
    exact ENNReal.le_tsum (f := fun β : M =>
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
        (chartTargetEuclid (I := I) (M := M) β)) α
  calc eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p_star
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
      ≤ ENNReal.ofReal C_α *
          eLpNorm f p_star
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := h_bridge
    _ ≤ ENNReal.ofReal C_α *
          (C_d *
            Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α)) := by gcongr
    _ ≤ ENNReal.ofReal C_α *
          (C_d * wkpNormChart (I := I) (M := M) 1 p_enn u) := by gcongr
    _ = K_α * wkpNormChart (I := I) (M := M) 1 p_enn u := by rw [hK_α_def]; ring

private theorem chartAtlasPOU_pou_decomp_subcritical
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (u : M → ℝ) (x : M) :
    u x = ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
      (I := I) (M := M),
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x * u x := by
  classical
  have hsum : ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
      (I := I) (M := M),
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x = 1 :=
    Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I) (M := M) x
  rw [← Finset.sum_mul, hsum, one_mul]

private noncomputable def perChartConst_pStar
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank ℝ E : ℝ)) : M → ℝ≥0∞ :=
  fun α => Classical.choose (perChart_eLpNorm_pStar_le (I := I) (M := M) g hp_one hp_dim α)

private lemma perChartConst_pStar_ne_top
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank ℝ E : ℝ)) (α : M) :
    perChartConst_pStar (I := I) (M := M) g hp_one hp_dim α ≠ ⊤ :=
  (Classical.choose_spec (perChart_eLpNorm_pStar_le (I := I) (M := M) g hp_one hp_dim α)).1

private lemma perChartConst_pStar_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank ℝ E : ℝ)) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u) :
    eLpNorm
        (fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)
        (ENNReal.ofReal
          ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
      perChartConst_pStar (I := I) (M := M) g hp_one hp_dim α *
        wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u :=
  (Classical.choose_spec (perChart_eLpNorm_pStar_le
    (I := I) (M := M) g hp_one hp_dim α)).2 hu_meas hu

theorem sobolev_closed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank ℝ E : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, Measurable u →
        MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u →
      eLpNorm u
        (ENNReal.ofReal
          ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M))
      ≤ ENNReal.ofReal C *
          wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u := by
  classical
  set p_real_star : ℝ := (Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)
    with hp_real_star_def
  set p_star : ℝ≥0∞ := ENNReal.ofReal p_real_star with hp_star_def
  set d : ℕ := Module.finrank ℝ E with hd_def
  have hd_pos : 0 < d := NeZero.pos d
  have hp_pos : 0 < p := by linarith
  have hp_star_real_pos : 0 < p_real_star := by
    rw [hp_real_star_def]
    apply div_pos (mul_pos (by exact_mod_cast hd_pos) hp_pos)
    linarith
  have hp_star_real_ge_p : p ≤ p_real_star := by
    rw [hp_real_star_def, le_div_iff₀ (by linarith : 0 < (d : ℝ) - p)]
    nlinarith [hp_pos]
  have hp_star_real_one : 1 ≤ p_real_star := le_trans hp_one hp_star_real_ge_p
  have hp_star_one : (1 : ℝ≥0∞) ≤ p_star := by
    rw [hp_star_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_star_real_one
  set S : Finset M := CalabiYau.RiemannianVolume.chartAtlasPOUFinset
    (I := I) (M := M) with hS_def
  set D : ℝ≥0∞ :=
    ∑ α ∈ S, perChartConst_pStar (I := I) (M := M) g hp_one hp_dim α
    with hD_def
  have hD_ne_top : D ≠ ⊤ := by
    rw [hD_def]
    apply ENNReal.sum_ne_top.mpr
    intro α _
    exact perChartConst_pStar_ne_top (I := I) (M := M) g hp_one hp_dim α
  refine ⟨max 1 D.toReal, ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left _ _)
  intro u hu_meas hu
  have h_eLpNorm_eq :
      eLpNorm u p_star (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) =
        eLpNorm (∑ α ∈ S, fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p_star
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := by
    refine eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S,
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x * u x
    exact chartAtlasPOU_pou_decomp_subcritical (I := I) (M := M) u x
  rw [h_eLpNorm_eq]
  have h_minkowski :
      eLpNorm (∑ α ∈ S, fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) p_star
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
        ∑ α ∈ S, eLpNorm
          (fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p_star
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) :=
    eLpNorm_sum_le hp_star_one
  refine h_minkowski.trans ?_
  have h_each : ∀ α ∈ S,
      eLpNorm
          (fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p_star
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
        perChartConst_pStar (I := I) (M := M) g hp_one hp_dim α *
          wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u := by
    intro α _
    exact perChartConst_pStar_bound (I := I) (M := M) g hp_one hp_dim α hu_meas hu
  have h_sum_le :
      (∑ α ∈ S, eLpNorm
          (fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p_star
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M))) ≤
        ∑ α ∈ S,
          perChartConst_pStar (I := I) (M := M) g hp_one hp_dim α *
            wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u :=
    Finset.sum_le_sum h_each
  refine h_sum_le.trans ?_
  rw [← Finset.sum_mul]
  change D * wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u ≤
    ENNReal.ofReal (max 1 D.toReal) *
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u
  gcongr
  have hD_eq : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hD_ne_top
  have h_max_le :
      ENNReal.ofReal D.toReal ≤ ENNReal.ofReal (max 1 D.toReal) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  rw [hD_eq] at h_max_le
  exact h_max_le

end Chart
end Sobolev
