-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/PointwiseInner/Algebra.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Defs
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section


noncomputable section

open Manifold Set Filter Bundle CalabiYau.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace CalabiYau.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S₁ S₂ T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x (S₁ + S₂) T =
      covariantTensorInnerPointwise (I := I) (M := M) s g x S₁ T +
        covariantTensorInnerPointwise (I := I) (M := M) s g x S₂ T := by
  induction s with
  | zero =>
      change (S₁ + S₂) _ * T _ = S₁ _ * T _ + S₂ _ * T _
      rw [add_apply]
      ring
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ, tensorInnerPointwise_0s_succ,
          tensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (S₁ + S₂).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
            S₁.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) +
              S₂.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              add_apply]
      rw [hcurry, ih]
      ring

theorem tensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T₁ T₂ : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S (T₁ + T₂) =
      covariantTensorInnerPointwise (I := I) (M := M) s g x S T₁ +
        covariantTensorInnerPointwise (I := I) (M := M) s g x S T₂ := by
  induction s with
  | zero =>
      change S _ * (T₁ + T₂) _ = S _ * T₁ _ + S _ * T₂ _
      rw [add_apply]
      ring
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ, tensorInnerPointwise_0s_succ,
          tensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (T₁ + T₂).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
            T₁.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) +
              T₂.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              add_apply]
      rw [hcurry, ih]
      ring

theorem tensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (c : ℝ) (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x (c • S) T =
      c * covariantTensorInnerPointwise (I := I) (M := M) s g x S T := by
  induction s with
  | zero =>
      change (c • S) _ * T _ = c * (S _ * T _)
      rw [smul_apply, smul_eq_mul]
      ring
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ, tensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • S).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
            c • S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              smul_apply]
      rw [hcurry, ih]
      ring

theorem tensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (c : ℝ) (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S (c • T) =
      c * covariantTensorInnerPointwise (I := I) (M := M) s g x S T := by
  induction s with
  | zero =>
      change S _ * (c • T) _ = c * (S _ * T _)
      rw [smul_apply, smul_eq_mul]
      ring
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ, tensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • T).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
            c • T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              smul_apply]
      rw [hcurry, ih]
      ring

theorem tensorInnerPointwise_0s_symm
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S T =
      covariantTensorInnerPointwise (I := I) (M := M) s g x T S := by
  induction s with
  | zero =>
      change S _ * T _ = T _ * S _
      ring
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ, tensorInnerPointwise_0s_succ]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      have hG :
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ j i =
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j := by
        have hherm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
        have := hherm.apply i j
        simpa [star_trivial] using this
      rw [ih, hG]

theorem tensorInnerPointwise_0s_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x 0 T = 0 := by
  have h := tensorInnerPointwise_0s_add_left (I := I) (M := M) g x s 0 0 T
  have h₀ : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

theorem tensorInnerPointwise_0s_zero_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S 0 = 0 := by
  rw [tensorInnerPointwise_0s_symm]
  exact tensorInnerPointwise_0s_zero_left (I := I) (M := M) g x s S

theorem tensorInnerPointwise_0s_zero_arity_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    0 ≤ covariantTensorInnerPointwise (I := I) (M := M) 0 g x S S := by
  change 0 ≤ S (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i)
  exact mul_self_nonneg _

theorem tensorInnerPointwise_0s_zero_arity_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) 0 g x S S = 0 ↔ S = 0 := by
  change S (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i) = 0 ↔ S = 0
  constructor
  · intro h
    have : S (fun i => Fin.elim0 i) = 0 := by
      rcases mul_self_eq_zero.mp h with h'
      exact h'
    ext v
    have hv : v = (fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    rw [hv]
    exact this
  · intro h
    rw [h]
    simp

private lemma tensorInnerPointwise_0s_sum_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι)
    (a : ι → ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x
        (∑ i ∈ A, a i • ψ i) T =
      ∑ i ∈ A, a i *
        covariantTensorInnerPointwise (I := I) (M := M) s g x (ψ i) T := by
  classical
  induction A using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_0s_zero_left]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi,
          tensorInnerPointwise_0s_add_left,
          tensorInnerPointwise_0s_smul_left,
          ih, Finset.sum_insert hi]

private lemma tensorInnerPointwise_0s_sum_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι)
    (a : ι → ℝ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x
        S (∑ i ∈ A, a i • ψ i) =
      ∑ i ∈ A, a i *
        covariantTensorInnerPointwise (I := I) (M := M) s g x S (ψ i) := by
  classical
  induction A using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_0s_zero_right]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi,
          tensorInnerPointwise_0s_add_right,
          tensorInnerPointwise_0s_smul_right,
          ih, Finset.sum_insert hi]

private lemma tensorInnerPointwise_0s_sum_sum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι₁ ι₂ : Type*}
    (A : Finset ι₁) (B : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (φ : ι₁ → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι₂ → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x
        (∑ i ∈ A, a i • φ i) (∑ j ∈ B, b j • ψ j) =
      ∑ i ∈ A, ∑ j ∈ B,
        a i * b j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x (φ i) (ψ j) := by
  rw [tensorInnerPointwise_0s_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [tensorInnerPointwise_0s_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

theorem tensorInnerPointwise_0s_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    0 ≤ covariantTensorInnerPointwise (I := I) (M := M) s g x S S := by
  induction s with
  | zero => exact tensorInnerPointwise_0s_zero_arity_nonneg (I := I) (M := M) g x S
  | succ s ih =>
      classical
      set n := Module.finrank ℝ E with hn_def
      set Ginv : Matrix (Fin n) (Fin n) ℝ :=
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
      have hGinv_psd : Ginv.PosSemidef := by
        simpa [hGinv] using gramMatrixAt_inv_posSemidef (I := I) (M := M) g x
      have hGinv_herm : Ginv.IsHermitian := hGinv_psd.isHermitian
      set Sfam : Fin n → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ :=
        fun i => S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) with hSfam_def
      have hspec := hGinv_herm.spectral_theorem
      set U : Matrix (Fin n) (Fin n) ℝ :=
        (hGinv_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU_def
      set μ : Fin n → ℝ := hGinv_herm.eigenvalues with hμ_def
      have hμ_nonneg : ∀ k, 0 ≤ μ k := hGinv_psd.eigenvalues_nonneg
      have hGinv_entry :
          ∀ i j : Fin n,
            Ginv i j = ∑ k : Fin n, μ k * (U i k * U j k) := by
        intro i j
        have hUDstar : Ginv = U * (Matrix.diagonal μ) * star U := by
          have := hspec
          simp only [Unitary.conjStarAlgAut_apply] at this
          have hofReal : (RCLike.ofReal ∘ hGinv_herm.eigenvalues :
              Fin n → ℝ) = hGinv_herm.eigenvalues := by
            funext k
            simp
          rw [hofReal] at this
          exact this
        rw [hUDstar]
        rw [Matrix.mul_apply]
        have hUD_entry : ∀ k : Fin n,
            (U * Matrix.diagonal μ) i k = U i k * μ k := by
          intro k
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single k]
          · simp [Matrix.diagonal]
          · intro l _ hl
            simp [Matrix.diagonal, hl]
          · intro hk
            exact absurd (Finset.mem_univ k) hk
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [hUD_entry k]
        have hstar : (star U) k j = U j k := by
          simp [Matrix.star_apply, star_trivial]
        rw [hstar]
        ring
      rw [tensorInnerPointwise_0s_succ]
      have hrewrite :
          ∑ i : Fin n, ∑ j : Fin n,
              Ginv i j *
                covariantTensorInnerPointwise (I := I) (M := M) s g x
                  (Sfam i) (Sfam j)
            = ∑ k : Fin n, μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x
                (∑ i : Fin n, U i k • Sfam i)
                (∑ j : Fin n, U j k • Sfam j) := by
        have hbilin :
            ∀ k : Fin n,
              covariantTensorInnerPointwise (I := I) (M := M) s g x
                  (∑ i : Fin n, U i k • Sfam i)
                  (∑ j : Fin n, U j k • Sfam j)
                = ∑ i : Fin n, ∑ j : Fin n,
                  U i k * U j k *
                    covariantTensorInnerPointwise (I := I) (M := M) s g x
                      (Sfam i) (Sfam j) :=
          fun k => by
            rw [tensorInnerPointwise_0s_sum_sum (g := g) (x := x) (s := s)
                  Finset.univ Finset.univ (fun i => U i k) (fun j => U j k)
                  Sfam Sfam]
        have hRHS :
            ∑ k : Fin n, μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x
                (∑ i : Fin n, U i k • Sfam i)
                (∑ j : Fin n, U j k • Sfam j)
            = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
                (μ k * (U i k * U j k)) *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hbilin k, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        rw [hRHS]
        have hLHS :
            ∑ i : Fin n, ∑ j : Fin n,
                Ginv i j *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j)
              = ∑ i : Fin n, ∑ j : Fin n,
                ∑ k : Fin n,
                  (μ k * (U i k * U j k)) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g x
                      (Sfam i) (Sfam j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hGinv_entry i j, Finset.sum_mul]
        rw [hLHS]
        have h_swap_inner :
            ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                (μ k * (U i k * U j k)) *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j)
              = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
                (μ k * (U i k * U j k)) *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]
        rw [h_swap_inner, Finset.sum_comm]
      rw [hrewrite]
      refine Finset.sum_nonneg ?_
      intro k _
      refine mul_nonneg (hμ_nonneg k) ?_
      exact ih (∑ i : Fin n, U i k • Sfam i)

theorem tensorInnerPointwise_0s_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) s g x S S = 0 ↔ S = 0 := by
  induction s with
  | zero =>
      exact tensorInnerPointwise_0s_zero_arity_eq_zero_iff
        (I := I) (M := M) g x S
  | succ s ih =>
      classical
      set n := Module.finrank ℝ E with hn_def
      set Ginv : Matrix (Fin n) (Fin n) ℝ :=
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
      have hGinv_herm : Ginv.IsHermitian :=
        gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
      set Sfam : Fin n → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ :=
        fun i => S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) with hSfam_def
      have hspec := hGinv_herm.spectral_theorem
      set U : Matrix (Fin n) (Fin n) ℝ :=
        (hGinv_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU_def
      set μ : Fin n → ℝ := hGinv_herm.eigenvalues with hμ_def
      have hμ_pos : ∀ k, 0 < μ k := by
        intro k
        simpa [hμ_def] using
          gramMatrixAt_inv_eigenvalues_pos (I := I) (M := M) g x k
      have hμ_nonneg : ∀ k, 0 ≤ μ k := fun k => le_of_lt (hμ_pos k)
      have hGinv_entry :
          ∀ i j : Fin n,
            Ginv i j = ∑ k : Fin n, μ k * (U i k * U j k) := by
        intro i j
        have hUDstar : Ginv = U * (Matrix.diagonal μ) * star U := by
          have := hspec
          simp only [Unitary.conjStarAlgAut_apply] at this
          have hofReal : (RCLike.ofReal ∘ hGinv_herm.eigenvalues :
              Fin n → ℝ) = hGinv_herm.eigenvalues := by
            funext k
            simp
          rw [hofReal] at this
          exact this
        rw [hUDstar]
        rw [Matrix.mul_apply]
        have hUD_entry : ∀ k : Fin n,
            (U * Matrix.diagonal μ) i k = U i k * μ k := by
          intro k
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single k]
          · simp [Matrix.diagonal]
          · intro l _ hl
            simp [Matrix.diagonal, hl]
          · intro hk
            exact absurd (Finset.mem_univ k) hk
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [hUD_entry k]
        have hstar : (star U) k j = U j k := by
          simp [Matrix.star_apply, star_trivial]
        rw [hstar]
        ring
      set W : Fin n → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ :=
        fun k => ∑ i : Fin n, U i k • Sfam i with hW_def
      have hW_nonneg : ∀ k, 0 ≤
          covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k) :=
        fun k => tensorInnerPointwise_0s_nonneg (I := I) (M := M) g x s (W k)
      have hrewrite :
          covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S S
            = ∑ k : Fin n, μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k) := by
        rw [tensorInnerPointwise_0s_succ]
        have hbilin :
            ∀ k : Fin n,
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k)
                = ∑ i : Fin n, ∑ j : Fin n,
                  U i k * U j k *
                    covariantTensorInnerPointwise (I := I) (M := M) s g x
                      (Sfam i) (Sfam j) := by
          intro k
          simp only [hW_def]
          rw [tensorInnerPointwise_0s_sum_sum (g := g) (x := x) (s := s)
                Finset.univ Finset.univ (fun i => U i k) (fun j => U j k)
                Sfam Sfam]
        have hRHS :
            ∑ k : Fin n, μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k)
              = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
                (μ k * (U i k * U j k)) *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hbilin k, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        rw [hRHS]
        have hLHS :
            ∑ i : Fin n, ∑ j : Fin n,
                Ginv i j *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j)
              = ∑ i : Fin n, ∑ j : Fin n,
                ∑ k : Fin n,
                  (μ k * (U i k * U j k)) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g x
                      (Sfam i) (Sfam j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hGinv_entry i j, Finset.sum_mul]
        change ∑ i : Fin n, ∑ j : Fin n,
            Ginv i j *
              covariantTensorInnerPointwise (I := I) (M := M) s g x
                (Sfam i) (Sfam j) = _
        rw [hLHS]
        have h_swap_inner :
            ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                (μ k * (U i k * U j k)) *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j)
              = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
                (μ k * (U i k * U j k)) *
                  covariantTensorInnerPointwise (I := I) (M := M) s g x
                    (Sfam i) (Sfam j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]
        rw [h_swap_inner, Finset.sum_comm]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hrewrite] at h
        have hterm_nonneg : ∀ k ∈ Finset.univ,
            0 ≤ μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k) :=
          fun k _ => mul_nonneg (hμ_nonneg k) (hW_nonneg k)
        have hterm_zero : ∀ k ∈ Finset.univ,
            μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp h
        have hWk_zero : ∀ k, W k = 0 := by
          intro k
          have hk : μ k *
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k) = 0 :=
            hterm_zero k (Finset.mem_univ k)
          have hinner_zero :
              covariantTensorInnerPointwise (I := I) (M := M) s g x (W k) (W k) = 0 := by
            rcases mul_eq_zero.mp hk with hμk | hinner
            · exact absurd hμk (ne_of_gt (hμ_pos k))
            · exact hinner
          exact (ih (W k)).mp hinner_zero
        have hUU_self :
            (hGinv_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
              star (hGinv_herm.eigenvectorUnitary :
                Matrix (Fin n) (Fin n) ℝ) = 1 := by
          exact Unitary.coe_mul_star_self
            (hGinv_herm.eigenvectorUnitary :
              unitary (Matrix (Fin n) (Fin n) ℝ))
        have hSfam_zero : ∀ j : Fin n, Sfam j = 0 := by
          intro j
          have hsmul_sum : ∀ (A : Finset (Fin n)) (c : ℝ)
              (f : Fin n → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ),
              c • (∑ i ∈ A, f i) = ∑ i ∈ A, c • f i := fun A c f => by
            refine ContinuousMultilinearMap.ext ?_
            intro w
            rw [smul_apply,
              sum_apply,
              sum_apply]
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [smul_apply]
          have hexpand : ∀ k : Fin n,
              (U j k) • W k = ∑ i : Fin n, (U j k * U i k) • Sfam i := by
            intro k
            simp only [hW_def]
            rw [hsmul_sum Finset.univ (U j k) (fun i => U i k • Sfam i)]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [smul_smul]
          have hsum : ∑ k : Fin n, (U j k) • W k
              = ∑ i : Fin n,
                (∑ k : Fin n, U j k * U i k) • Sfam i := by
            rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_smul]
          have hcoef : ∀ i : Fin n,
              (∑ k : Fin n, U j k * U i k)
                = ((U * star U : Matrix (Fin n) (Fin n) ℝ)) j i := by
            intro i
            rw [Matrix.mul_apply]
            refine Finset.sum_congr rfl ?_
            intro k _
            have hstar : (star U) k i = U i k := by
              simp [Matrix.star_apply, star_trivial]
            rw [hstar]
          have hUUstar :
              (U * star U : Matrix (Fin n) (Fin n) ℝ)
                = (1 : Matrix (Fin n) (Fin n) ℝ) := by
            simp only [hU_def]
            exact hUU_self
          have hcoef_one : ∀ i : Fin n,
              (∑ k : Fin n, U j k * U i k) = if j = i then 1 else 0 := by
            intro i
            rw [hcoef i, hUUstar]
            simp [Matrix.one_apply]
          have hlhs_zero : ∑ k : Fin n, (U j k) • W k = 0 := by
            refine Finset.sum_eq_zero ?_
            intro k _
            rw [hWk_zero k]
            simp
          rw [hlhs_zero] at hsum
          have hrhs :
              ∑ i : Fin n, (∑ k : Fin n, U j k * U i k) • Sfam i = Sfam j := by
            rw [Finset.sum_congr rfl (fun i _ => by rw [hcoef_one i])]
            have h_ite_eq : ∀ i : Fin n,
                (if j = i then (1 : ℝ) else 0) • Sfam i
                  = if j = i then Sfam i else 0 := by
              intro i
              by_cases hji : j = i
              · simp [hji]
              · simp [hji]
            rw [Finset.sum_congr rfl (fun i _ => h_ite_eq i)]
            rw [Finset.sum_ite_eq Finset.univ j (fun i => Sfam i)]
            simp
          rw [hrhs] at hsum
          exact hsum.symm
        have hcurry_zero : S.curryLeft = 0 := by
          refine ContinuousLinearMap.ext ?_
          intro v
          have hexp : v = ∑ i : Fin n,
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr v i) • ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) :=
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_repr v).symm
          rw [hexp]
          rw [map_sum]
          refine Finset.sum_eq_zero ?_
          intro i _
          rw [ContinuousLinearMap.map_smul]
          have : S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) = 0 := by
            have := hSfam_zero i
            rwa [hSfam_def] at this
          rw [this]
          simp
        have hS_uncurry : S = S.curryLeft.uncurryLeft :=
          (ContinuousMultilinearMap.uncurry_curryLeft S).symm
        rw [hS_uncurry, hcurry_zero]
        ext v
        simp [ContinuousLinearMap.uncurryLeft_apply]
      · rw [h]
        exact tensorInnerPointwise_0s_zero_left
          (I := I) (M := M) g x (s + 1) 0

theorem tensorInnerPointwise_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S₁ S₂ T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x (S₁ + S₂) T =
      tensorInnerPointwise (I := I) (M := M) g r s x S₁ T +
        tensorInnerPointwise (I := I) (M := M) g r s x S₂ T := by
  unfold tensorInnerPointwise
  rw [ContinuousLinearMap.map_add]
  exact tensorInnerPointwise_0s_add_left (I := I) (M := M) g x (r + s) _ _ _

theorem tensorInnerPointwise_zero_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x 0 T = 0 := by
  have h := tensorInnerPointwise_add_left
    (I := I) (M := M) g r s x 0 0 T
  have h₀ : (0 : TensorRSModel r s ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

end CalabiYau.L2

end
