-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Scalar/Spectrum.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Spectral.Scalar.Resolvent
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

lemma norm_H1ComplToLp_apply_le (g : SmoothRiemannianMetric I M)
    (v : H1Compl g) :
    ‖h1ComplToLp (I := I) (M := M) g v‖ ≤ ‖v‖ := by
  refine UniformSpace.Completion.induction_on (α := SmoothScalar g) v ?_ ?_
  · have h_cont_lhs : Continuous (fun w : H1Compl g =>
        ‖h1ComplToLp (I := I) (M := M) g w‖) :=
      (h1ComplToLp (I := I) (M := M) g).continuous.norm
    have h_cont_rhs : Continuous (fun w : H1Compl g => ‖w‖) := continuous_norm
    exact isClosed_le h_cont_lhs h_cont_rhs
  · intro a
    have h_eq : h1ComplToLp (I := I) (M := M) g
          ((a : H1Compl g)) =
        smoothToLp (I := I) (M := M) g a := by
      have h := h1ComplToLp_smoothToH1Compl (I := I) (M := M) g a
      simpa using h
    have h_norm : ‖((a : H1Compl g) : H1Compl g)‖ = ‖a‖ := by
      change ‖(UniformSpace.Completion.toCompl a : H1Compl g)‖ = ‖a‖
      exact UniformSpace.Completion.norm_coe a
    rw [h_eq, h_norm]
    exact a.norm_smoothToLp_le

noncomputable def resolventEigenspace (g : SmoothRiemannianMetric I M) (μ : ℝ) :
    Submodule ℝ (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
  Module.End.eigenspace
    ((resolventL2 (I := I) (M := M) g).toLinearMap) μ

lemma mem_resolventEigenspace_iff (g : SmoothRiemannianMetric I M) (μ : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    u ∈ resolventEigenspace (I := I) (M := M) g μ ↔
      resolventL2 (I := I) (M := M) g u = μ • u := by
  unfold resolventEigenspace
  rw [Module.End.mem_eigenspace_iff]
  rfl

theorem resolventEigenspace_finiteDim
    (g : SmoothRiemannianMetric I M)
    (hCompact : IsCompactOperator (resolventL2 (I := I) (M := M) g))
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (resolventEigenspace (I := I) (M := M) g μ) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace hCompact μ hμ

theorem resolventEigenspaces_iSup_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M)
    (hCompact : IsCompactOperator (resolventL2 (I := I) (M := M) g)) :
    (⨆ μ : ℝ, resolventEigenspace (I := I) (M := M) g μ)ᗮ = ⊥ := by
  have hSymm : (resolventL2 (I := I) (M := M) g).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventL2_isSelfAdjoint (I := I) (M := M) g)
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    hCompact hSymm

def laplacianEigenvalueOf (μ : ℝ) : ℝ := (1 - μ) / μ

private lemma mul_norm_sq_eq_h1Norm_resolvent_sq
    (g : SmoothRiemannianMetric I M)
    {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    μ * (‖u‖ ^ 2) =
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 := by
  have hRu : resolventL2 (I := I) (M := M) g u = μ • u :=
    (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
  have h_h1 : ⟪resolvent (I := I) (M := M) g u,
        resolvent (I := I) (M := M) g u⟫_ℝ =
      ⟪h1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g u),
        u⟫_ℝ :=
    resolvent_inner_eq_lpFunctional (I := I) (M := M) g u
      (resolvent (I := I) (M := M) g u)
  have h_lhs_to_norm : ⟪resolvent (I := I) (M := M) g u,
        resolvent (I := I) (M := M) g u⟫_ℝ =
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h_replace : h1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u) =
      resolventL2 (I := I) (M := M) g u := by
    rw [resolventL2_apply]
  rw [h_lhs_to_norm] at h_h1
  rw [h_replace, hRu] at h_h1
  rw [real_inner_smul_left] at h_h1
  rw [real_inner_self_eq_norm_sq] at h_h1
  linarith

theorem resolvent_eigenvalue_nonneg
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) (hu_ne : u ≠ 0) :
    0 ≤ μ := by
  have h := mul_norm_sq_eq_h1Norm_resolvent_sq (I := I) (M := M) g hu
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have h_rhs_nn : 0 ≤ ‖resolvent (I := I) (M := M) g u‖ ^ 2 := sq_nonneg _
  have h_prod_nn : 0 ≤ μ * (‖u‖ ^ 2) := h.symm ▸ h_rhs_nn
  exact (mul_nonneg_iff_of_pos_right hu_pos).mp h_prod_nn

theorem resolvent_eigenvalue_le_one
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) (hu_ne : u ≠ 0) :
    μ ≤ 1 := by
  have h_var := mul_norm_sq_eq_h1Norm_resolvent_sq (I := I) (M := M) g hu
  have h_norm_bound :
      ‖h1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g u)‖ ≤
        ‖resolvent (I := I) (M := M) g u‖ :=
    norm_H1ComplToLp_apply_le (I := I) (M := M) g
      (resolvent (I := I) (M := M) g u)
  have hRu_eq_smul : h1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u) = μ • u := by
    rw [show h1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g u) =
        resolventL2 (I := I) (M := M) g u from by rw [resolventL2_apply]]
    exact (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
  have h_norm_smul : ‖h1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u)‖ = |μ| * ‖u‖ := by
    rw [hRu_eq_smul, norm_smul]
    rfl
  have h_abs_le_norm : |μ| * ‖u‖ ≤ ‖resolvent (I := I) (M := M) g u‖ :=
    h_norm_smul ▸ h_norm_bound
  have h_sq_bound : (|μ| * ‖u‖) ^ 2 ≤
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 := by
    have h_lhs_nn : 0 ≤ |μ| * ‖u‖ := by positivity
    nlinarith [h_abs_le_norm, h_lhs_nn]
  have h_chain : (|μ| * ‖u‖) ^ 2 ≤ μ * ‖u‖ ^ 2 := h_var ▸ h_sq_bound
  have h_expand : (|μ| * ‖u‖) ^ 2 = μ ^ 2 * ‖u‖ ^ 2 := by
    rw [mul_pow]
    have hsq : |μ| ^ 2 = μ ^ 2 := sq_abs μ
    rw [hsq]
  have h_chain' : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_expand ▸ h_chain
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have hμ_sq_le : μ ^ 2 ≤ μ := by
    have h1 : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_chain'
    nlinarith [hu_pos]
  have hμ_nn : 0 ≤ μ :=
    resolvent_eigenvalue_nonneg (I := I) (M := M) g hu hu_ne
  by_contra h_not
  push Not at h_not
  have h_mu_gt_one : 1 < μ := h_not
  have h_mu_pos : 0 < μ := lt_trans zero_lt_one h_mu_gt_one
  have h_lt : μ < μ ^ 2 := by nlinarith
  linarith

theorem laplacianOp_of_resolventEigenvector_lift
    (g : SmoothRiemannianMetric I M) {μ : ℝ} (hμ : μ ≠ 0)
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    laplacianOp (I := I) (M := M) g
        ⟨μ⁻¹ • resolvent (I := I) (M := M) g u,
          (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
            ⟨μ⁻¹ • u, by
              rw [(resolvent (I := I) (M := M) g).map_smul]⟩⟩ =
      -(laplacianEigenvalueOf μ) • u := by
  have hRu : resolventL2 (I := I) (M := M) g u = μ • u :=
    (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
  have h_eq : (μ⁻¹ • resolvent (I := I) (M := M) g u :
        H1Compl (I := I) (M := M) g) =
      resolvent (I := I) (M := M) g (μ⁻¹ • u) := by
    rw [(resolvent (I := I) (M := M) g).map_smul]
  rw [show (⟨μ⁻¹ • resolvent (I := I) (M := M) g u,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨μ⁻¹ • u, by
            rw [(resolvent (I := I) (M := M) g).map_smul]⟩⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g (μ⁻¹ • u),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨μ⁻¹ • u, rfl⟩⟩ from by
    apply Subtype.ext
    exact h_eq]
  rw [laplacianOp_resolvent]
  have h_HRl : h1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g (μ⁻¹ • u)) =
      u := by
    rw [(resolvent (I := I) (M := M) g).map_smul]
    rw [(h1ComplToLp (I := I) (M := M) g).map_smul]
    have h_replace : h1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g u) =
        resolventL2 (I := I) (M := M) g u := by
      rw [resolventL2_apply]
    rw [h_replace, hRu, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  rw [h_HRl]
  have h_eq_smul : u - (μ⁻¹ • u) = (1 - μ⁻¹) • u := by
    rw [sub_smul, one_smul]
  rw [h_eq_smul]
  unfold laplacianEigenvalueOf
  have h_alg : (1 - μ⁻¹) = -((1 - μ) / μ) := by
    field_simp
    ring
  rw [h_alg, neg_smul]

private lemma exists_unit_eigenvector
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((resolventL2 (I := I) (M := M) g).toLinearMap) μ) :
    ∃ u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      u ∈ resolventEigenspace (I := I) (M := M) g μ ∧ ‖u‖ = 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := hμ.exists_hasEigenvector
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [mem_resolventEigenspace_iff]
    have hRu : resolventL2 (I := I) (M := M) g u = μ • u := by
      have hu_in : u ∈ resolventEigenspace (I := I) (M := M) g μ := hu_mem
      exact (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu_in
    rw [(resolventL2 (I := I) (M := M) g).map_smul, hRu, smul_comm]
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt hu_pos)

private lemma resolvent_eigenvectors_orthogonal
    (g : SmoothRiemannianMetric I M) {μ ν : ℝ} (hμν : μ ≠ ν)
    {u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ)
    (hv : v ∈ resolventEigenspace (I := I) (M := M) g ν) :
    ⟪u, v⟫_ℝ = 0 := by
  have hSymm : ((resolventL2 (I := I) (M := M) g).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventL2_isSelfAdjoint (I := I) (M := M) g)
  have hortho := hSymm.orthogonalFamily_eigenspaces hμν
  exact hortho ⟨u, hu⟩ ⟨v, hv⟩

private lemma resolventL2_apply_eigenvector
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    resolventL2 (I := I) (M := M) g u = μ • u :=
  (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu

private lemma resolventL2_image_separated_of_distinct_eigenvalues
    (g : SmoothRiemannianMetric I M)
    {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → ℝ} (hf_inj : Function.Injective f)
    (hf_size : ∀ n, ε ≤ |f n|)
    (v : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (hv_mem : ∀ n, v n ∈ resolventEigenspace (I := I) (M := M) g (f n))
    (hv_norm : ∀ n, ‖v n‖ = 1) :
    ∀ n m : ℕ, n ≠ m →
      Real.sqrt 2 * ε ≤ ‖resolventL2 (I := I) (M := M) g (v n) -
                         resolventL2 (I := I) (M := M) g (v m)‖ := by
  intro n m hnm
  have hRn : resolventL2 (I := I) (M := M) g (v n) = f n • v n :=
    resolventL2_apply_eigenvector (I := I) (M := M) g (hv_mem n)
  have hRm : resolventL2 (I := I) (M := M) g (v m) = f m • v m :=
    resolventL2_apply_eigenvector (I := I) (M := M) g (hv_mem m)
  have hfne : f n ≠ f m := fun h => hnm (hf_inj h)
  have hortho : ⟪v n, v m⟫_ℝ = 0 :=
    resolvent_eigenvectors_orthogonal (I := I) (M := M) g hfne
      (hv_mem n) (hv_mem m)
  have h_norm_sq : ‖f n • v n - f m • v m‖ ^ 2 =
      (f n) ^ 2 + (f m) ^ 2 := by
    rw [@norm_sub_sq_real]
    rw [norm_smul, norm_smul, mul_pow, mul_pow]
    rw [hv_norm n, hv_norm m]
    rw [one_pow, mul_one, mul_one]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [sq_abs, sq_abs]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [hortho, mul_zero, mul_zero]
    ring
  have h_norm_sq_lb : 2 * ε ^ 2 ≤ ‖f n • v n - f m • v m‖ ^ 2 := by
    rw [h_norm_sq]
    have h1 : ε ^ 2 ≤ (f n) ^ 2 := by
      have h_abs := hf_size n
      have h_abs_sq : ε ^ 2 ≤ |f n| ^ 2 := by
        have : 0 ≤ ε := hε.le
        nlinarith [hf_size n, sq_nonneg (|f n| - ε)]
      have h_sq_abs : |f n| ^ 2 = (f n) ^ 2 := sq_abs _
      linarith
    have h2 : ε ^ 2 ≤ (f m) ^ 2 := by
      have h_abs := hf_size m
      have h_abs_sq : ε ^ 2 ≤ |f m| ^ 2 := by
        have : 0 ≤ ε := hε.le
        nlinarith [hf_size m, sq_nonneg (|f m| - ε)]
      have h_sq_abs : |f m| ^ 2 = (f m) ^ 2 := sq_abs _
      linarith
    linarith
  have h_lhs_nn : 0 ≤ ‖f n • v n - f m • v m‖ := norm_nonneg _
  have h_target : Real.sqrt (2 * ε ^ 2) ≤ ‖f n • v n - f m • v m‖ := by
    rw [show ‖f n • v n - f m • v m‖ =
        Real.sqrt (‖f n • v n - f m • v m‖ ^ 2) from
      (Real.sqrt_sq h_lhs_nn).symm]
    exact Real.sqrt_le_sqrt h_norm_sq_lb
  have h_sqrt_eq : Real.sqrt (2 * ε ^ 2) = Real.sqrt 2 * ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (ε ^ 2 : ℝ) = ε * ε from sq ε]
    rw [Real.sqrt_mul_self hε.le]
  rw [hRn, hRm]
  rw [← h_sqrt_eq]
  exact h_target

theorem resolvent_eigenvalues_finite_above
    (g : SmoothRiemannianMetric I M)
    (hCompact : IsCompactOperator (resolventL2 (I := I) (M := M) g))
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite { μ : ℝ |
      Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } := by
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  let f : ℕ ↪ _ := h_inf.natEmbedding
  set f' : ℕ → ℝ := fun n => (f n : ℝ)
  have hf_eig : ∀ n, Module.End.HasEigenvalue
      ((resolventL2 (I := I) (M := M) g).toLinearMap) (f' n) := fun n =>
    (f n).property.1
  have hf_size : ∀ n, ε ≤ |f' n| := fun n => (f n).property.2
  have hf_inj' : Function.Injective f' := by
    intro n m h
    have h1 : f n = f m := by
      apply Subtype.ext; exact h
    exact Function.Embedding.injective f h1
  choose v hv_mem hv_norm using fun n =>
    exists_unit_eigenvector (I := I) (M := M) g (hf_eig n)
  have h_sep := resolventL2_image_separated_of_distinct_eigenvalues
    (I := I) (M := M) g hε hf_inj' hf_size v hv_mem hv_norm
  have h_v_in_ball : ∀ n, v n ∈ Metric.closedBall
      (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [hv_norm n]
  obtain ⟨K, hK_compact, hK_subset⟩ :=
    hCompact.image_closedBall_subset_compact (1 : ℝ)
  have h_R_v_in_K : ∀ n, resolventL2 (I := I) (M := M) g (v n) ∈ K := by
    intro n
    apply hK_subset
    refine ⟨v n, h_v_in_ball n, ?_⟩
    rfl
  obtain ⟨y, hyK, ψ, hψ_mono, hψy⟩ := hK_compact.tendsto_subseq h_R_v_in_K
  have h_cauchy : CauchySeq (fun n =>
      resolventL2 (I := I) (M := M) g (v (ψ n))) :=
    hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at h_cauchy
  have h_sep_pos : 0 < Real.sqrt 2 * ε := by
    have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    exact mul_pos h_sqrt2_pos hε
  obtain ⟨N, hN⟩ := h_cauchy (Real.sqrt 2 * ε) h_sep_pos
  have h_dist : dist (resolventL2 (I := I) (M := M) g (v (ψ (N + 1))))
        (resolventL2 (I := I) (M := M) g (v (ψ N))) < Real.sqrt 2 * ε := by
    have := hN (N + 1) (Nat.le_succ N)
    exact this
  have h_ne : ψ (N + 1) ≠ ψ N := by
    intro h_eq
    have h_lt : ψ N < ψ (N + 1) := hψ_mono (Nat.lt_succ_self N)
    rw [h_eq] at h_lt
    exact lt_irrefl _ h_lt
  have h_sep_specific := h_sep (ψ (N + 1)) (ψ N) h_ne
  rw [show dist (resolventL2 (I := I) (M := M) g (v (ψ (N + 1))))
        (resolventL2 (I := I) (M := M) g (v (ψ N))) =
      ‖resolventL2 (I := I) (M := M) g (v (ψ (N + 1))) -
        resolventL2 (I := I) (M := M) g (v (ψ N))‖ from
    dist_eq_norm _ _] at h_dist
  linarith [h_sep_specific, h_dist]

end Laplacian
end Analysis
end CalabiYau

end
