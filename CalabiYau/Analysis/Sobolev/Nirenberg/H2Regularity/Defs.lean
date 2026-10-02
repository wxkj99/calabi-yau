-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/H2Regularity/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.WeakDerivatives
public import CalabiYau.Analysis.DeGiorgi.EllipticCoefficients

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem diffQuot_bound_of_smooth_compactSupport
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hf_support : HasCompactSupport f)
    (i : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ h : ℝ, ∀ x : E,
        |Sobolev.diffQuot i h f x| ≤ L := by
  obtain ⟨L, hL_nn, hLip⟩ :=
    Sobolev.lipschitz_of_contDiff_compactSupport
      (d := d) hf hf_support
  refine ⟨L, hL_nn, fun h x => ?_⟩
  by_cases hh : h = 0
  · simp [Sobolev.diffQuot, hh, hL_nn]
  · rw [Sobolev.diffQuot_apply_of_ne (d := d) i hh f x]
    have hLip_apply :
        ‖f (x + h • EuclideanSpace.single i 1) - f x‖ ≤
          L * ‖x + h • EuclideanSpace.single i 1 - x‖ := hLip _ _
    have hsimp : x + h • EuclideanSpace.single i 1 - x =
        h • EuclideanSpace.single i 1 := by
      rw [add_sub_cancel_left]
    rw [hsimp] at hLip_apply
    have hsing_norm :
        ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ = 1 := by simp
    have hnorm_smul :
        ‖h • EuclideanSpace.single i (1 : ℝ)‖ = |h| := by
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    rw [hnorm_smul] at hLip_apply
    rw [abs_div]
    have habs_h : 0 < |h| := abs_pos.mpr hh
    rw [div_le_iff₀ habs_h]
    have h_lhs_norm :
        |f (x + h • EuclideanSpace.single i 1) - f x| =
          ‖f (x + h • EuclideanSpace.single i 1) - f x‖ :=
      (Real.norm_eq_abs _).symm
    rw [h_lhs_norm]
    exact hLip_apply

structure SmoothEllipticBilinearForm
    (d : ℕ) [NeZero d] (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ
  c : EuclideanSpace ℝ (Fin d) → ℝ
  symm : ∀ x i j, a x i j = a x j i
  smooth_a : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => a x i j)
  smooth_c : ContDiff ℝ (⊤ : ℕ∞) c
  lam : ℝ
  capLam : ℝ
  ellipticity_pos : 0 < lam
  ellipticity_le_upper : lam ≤ capLam
  coercive : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin d),
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (a x) ξ⟫_ℝ

namespace SmoothEllipticBilinearForm

theorem contDiff_a {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => B.a x i j) :=
  B.smooth_a i j

theorem continuous_a {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (i j : Fin d) :
    Continuous (fun x : E => B.a x i j) :=
  (B.smooth_a i j).continuous

theorem continuous_c {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    Continuous B.c :=
  B.smooth_c.continuous

theorem lam_nonneg {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 ≤ B.lam := B.ellipticity_pos.le

theorem capLam_pos {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 < B.capLam := lt_of_lt_of_le B.ellipticity_pos B.ellipticity_le_upper

theorem capLam_nonneg {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) :
    0 ≤ B.capLam := B.capLam_pos.le

theorem bounded_a_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin d, ∀ x ∈ K, |B.a x i j| ≤ M := by
  classical
  have h_each : ∀ ij : Fin d × Fin d, ∃ Mij : ℝ, 0 ≤ Mij ∧
      ∀ x ∈ K, |B.a x ij.1 ij.2| ≤ Mij := by
    intro ij
    rcases hK.bddAbove_image (B.continuous_a ij.1 ij.2 |>.abs.continuousOn) with ⟨Mij, hMij⟩
    refine ⟨max Mij 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hMij (mem_image_of_mem _ hx)
    exact h.trans (le_max_left _ _)
  let pairBound : Fin d × Fin d → ℝ := fun ij => Classical.choose (h_each ij)
  have pairBound_nn : ∀ ij, 0 ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).1
  have pairBound_le : ∀ ij : Fin d × Fin d, ∀ x ∈ K,
      |B.a x ij.1 ij.2| ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).2
  let M : ℝ := ∑ ij : Fin d × Fin d, pairBound ij
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun ij _ => pairBound_nn ij)
  refine ⟨M, hM_nn, fun i j x hx => ?_⟩
  have hsingle : pairBound (i, j) ≤ M := by
    refine Finset.single_le_sum (f := pairBound) (s := Finset.univ) ?_ (Finset.mem_univ (i, j))
    intro ij _
    exact pairBound_nn ij
  exact (pairBound_le (i, j) x hx).trans hsingle

theorem bounded_c_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |B.c x| ≤ M := by
  rcases hK.bddAbove_image (B.continuous_c.abs.continuousOn) with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hM (mem_image_of_mem _ hx)
  exact h.trans (le_max_left _ _)

theorem bounded_fderiv_a_on_compact {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (k : Fin d) {K : Set E} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin d, ∀ x ∈ K,
      |(fderiv ℝ (fun x : E => B.a x i j) x) (EuclideanSpace.single k 1)| ≤ M := by
  classical
  have h_each : ∀ ij : Fin d × Fin d, ∃ Mij : ℝ, 0 ≤ Mij ∧
      ∀ x ∈ K, |(fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x)
        (EuclideanSpace.single k 1)| ≤ Mij := by
    intro ij
    have hcont : Continuous
        (fun x : E => (fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x)
          (EuclideanSpace.single k 1)) :=
      ((B.contDiff_a ij.1 ij.2).continuous_fderiv (by simp)).clm_apply continuous_const
    rcases hK.bddAbove_image hcont.abs.continuousOn with ⟨Mij, hMij⟩
    refine ⟨max Mij 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hMij (mem_image_of_mem _ hx)
    exact h.trans (le_max_left _ _)
  let pairBound : Fin d × Fin d → ℝ := fun ij => Classical.choose (h_each ij)
  have pairBound_nn : ∀ ij, 0 ≤ pairBound ij := fun ij => (Classical.choose_spec (h_each ij)).1
  have pairBound_le : ∀ ij : Fin d × Fin d, ∀ x ∈ K,
      |(fderiv ℝ (fun y : E => B.a y ij.1 ij.2) x) (EuclideanSpace.single k 1)| ≤
        pairBound ij :=
    fun ij => (Classical.choose_spec (h_each ij)).2
  let M : ℝ := ∑ ij : Fin d × Fin d, pairBound ij
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun ij _ => pairBound_nn ij)
  refine ⟨M, hM_nn, fun i j x hx => ?_⟩
  have hsingle : pairBound (i, j) ≤ M := by
    refine Finset.single_le_sum (f := pairBound) (s := Finset.univ) ?_ (Finset.mem_univ (i, j))
    intro ij _
    exact pairBound_nn ij
  exact (pairBound_le (i, j) x hx).trans hsingle

def principalIntegrand {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u v : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    B.a x i j *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ v x) (EuclideanSpace.single j 1))

def bilin {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u v : E → ℝ) : ℝ :=
  ∫ x in Ω, B.principalIntegrand u v x + B.c x * u x * v x

def IsSmoothWeakSolution {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u f : E → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    B.bilin u φ = ∫ x in Ω, f x * φ x

theorem principalIntegrand_symm {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u v : E → ℝ) (x : E) :
    B.principalIntegrand u v x = B.principalIntegrand v u x := by
  classical
  unfold principalIntegrand
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [B.symm x j i]
  ring

theorem continuous_principalIntegrand {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (B.principalIntegrand u v) := by
  classical
  unfold principalIntegrand
  refine continuous_finsetSum _ ?_
  intro i _
  refine continuous_finsetSum _ ?_
  intro j _
  refine ((B.continuous_a i j).mul ?_).mul ?_
  · exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const

theorem continuous_bilin_integrand {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (fun x => B.principalIntegrand u v x + B.c x * u x * v x) :=
  (B.continuous_principalIntegrand hu hv).add
    ((B.continuous_c.mul hu.continuous).mul hv.continuous)

def gradientVec (u : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i : Fin d => (fderiv ℝ u x) (EuclideanSpace.single i 1))

theorem principalIntegrand_self_eq_inner {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ) (x : E) :
    B.principalIntegrand u u x =
      ⟪gradientVec u x, DeGiorgi.matMulE (B.a x) (gradientVec u x)⟫_ℝ := by
  classical
  set ξ : E := gradientVec u x with hξ
  set V : Fin d → ℝ := fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1) with hV
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a x) ξ⟫_ℝ =
        (fun j => (B.a x).mulVec V j) ⬝ᵥ V := by
    have hξofLp : ξ.ofLp = V := by simp [hξ, hV, gradientVec]
    have hmatofLp : (DeGiorgi.matMulE (B.a x) ξ).ofLp = (B.a x).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξofLp]
    change (DeGiorgi.matMulE (B.a x) ξ).ofLp ⬝ᵥ star ξ.ofLp =
      (fun j => (B.a x).mulVec V j) ⬝ᵥ V
    rw [hmatofLp, hξofLp]
    change (B.a x).mulVec V ⬝ᵥ (star V) = (B.a x).mulVec V ⬝ᵥ V
    rfl
  rw [h_inner]
  unfold principalIntegrand
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  change ∑ i, B.a x i j * V i * V j = (B.a x).mulVec V j * V j
  rw [show ((B.a x).mulVec V) j = ∑ i, B.a x j i * V i from rfl]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [B.symm x i j]

theorem principalIntegrand_self_ge {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {x : E} (hx : x ∈ Ω) :
    B.lam * ‖gradientVec u x‖ ^ 2 ≤
      B.principalIntegrand u u x := by
  rw [principalIntegrand_self_eq_inner]
  exact B.coercive x hx (gradientVec u x)

omit [NeZero d] in
theorem gradientVec_norm_sq_eq_sum (u : E → ℝ) (x : E) :
    ‖gradientVec u x‖ ^ 2 =
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2 := by
  unfold gradientVec
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  change ‖(fderiv ℝ u x) (EuclideanSpace.single i 1)‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]

theorem bilin_integrand_self_ge {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {x : E} (hx : x ∈ Ω) :
    B.lam * ‖gradientVec u x‖ ^ 2 + B.c x * u x * u x ≤
      B.principalIntegrand u u x + B.c x * u x * u x := by
  have h := B.principalIntegrand_self_ge u hx
  linarith

end SmoothEllipticBilinearForm

omit [NeZero d] in
theorem diffQuot_mul
    (i : Fin d) (h : ℝ) (f g : E → ℝ) :
    Sobolev.diffQuot i h (fun x => f x * g x) =
      fun x =>
        (Sobolev.translate i h f x) *
            (Sobolev.diffQuot i h g x) +
          (Sobolev.diffQuot i h f x) * g x := by
  ext x
  by_cases hh : h = 0
  · subst hh
    simp [Sobolev.diffQuot,
          Sobolev.translate]
  · simp only [Sobolev.diffQuot,
               Sobolev.translate, hh, ↓reduceIte]
    field_simp
    ring

omit [NeZero d] in
theorem diffQuot_coeff_apply
    (k : Fin d) (h : ℝ) (a v : E → ℝ) (x : E) :
    Sobolev.diffQuot k h (fun y => a y * v y) x =
      Sobolev.translate k h a x *
          Sobolev.diffQuot k h v x +
        Sobolev.diffQuot k h a x * v x := by
  have h := diffQuot_mul (d := d) k h a v
  exact congrArg (fun f : E → ℝ => f x) h

end Sobolev.NirenbergEuclidean
