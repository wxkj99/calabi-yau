module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.CompactSupport

/-!
# Differentiating compactly supported convolution

Hirsch, *Differential Topology*, §2, Theorem 2.3, pp. 46–49: integration
by parts transfers derivatives through convolution to the compactly supported
C² factor. This is an identity of full real Fréchet jets, with their native
operator norms, not an identity valid only for orthonormal coordinates.
-/

@[expose] public section

open scoped ContDiff Convolution Topology
open MeasureTheory MeasureTheory.Measure

private theorem euclideanC2Convolution_zero_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E}
    (A : EuclideanC2ConvolutionData E f U) (hf : ContDiff ℝ 2 f)
    (j : ℕ) (x : E) :
    iteratedFDeriv ℝ 0 (A.approximation j) x =
      ∫ y, ((A.kernel j).normed (volume : Measure E) y) •
        iteratedFDeriv ℝ 0 f (x - y) ∂(volume : Measure E) := by
  let k := (A.kernel j).normed (volume : Measure E)
  let e := continuousMultilinearCurryFin0 ℝ E ℝ
  have hk : HasCompactSupport k := (A.kernel j).hasCompactSupport_normed
  have hcont : Continuous (fun y : E => k y • f (x - y)) := by
    change Continuous (fun y : E => (A.kernel j).normed (volume : Measure E) y * f (x - y))
    exact (A.kernel j).continuous_normed.mul
      (hf.continuous.comp (continuous_const.sub continuous_id))
  have hI : Integrable (fun y : E => k y • f (x - y)) (volume : Measure E) :=
    hcont.integrable_of_hasCompactSupport hk.smul_right
  rw [iteratedFDeriv_zero_eq_comp]
  change e.symm (A.approximation j x) = _
  rw [A.convolution_eq j, convolution_lsmul]
  change e.symm.toContinuousLinearMap (∫ y, k y • f (x - y) ∂(volume : Measure E)) = _
  rw [← e.symm.toContinuousLinearMap.integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards with y
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, map_smul]
  change k y • e.symm (f (x - y)) = k y • e.symm (f (x - y))
  rfl

private theorem convolution_parametric_hasFDerivAt
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (k : E → ℝ) (hk : HasCompactSupport k) (hkc : Continuous k)
    (g : E → G) (hg : ContDiff ℝ 1 g) (x₀ : E) (C : ℝ)
    (hbound : ∀ x ∈ Metric.closedBall x₀ 1, ∀ y ∈ tsupport k,
      ‖fderiv ℝ g (x - y)‖ ≤ C) :
    HasFDerivAt (fun x => ∫ y, k y • g (x - y) ∂(volume : Measure E))
      (∫ y, k y • fderiv ℝ g (x₀ - y) ∂(volume : Measure E)) x₀ := by
  let D : E → E → E →L[ℝ] G := fun x y => k y • fderiv ℝ g (x - y)
  have hgcont : Continuous g := hg.continuous
  have hdfcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hFcont (x : E) : Continuous (fun y => k y • g (x - y)) := by
    exact hkc.smul (hgcont.comp (continuous_const.sub continuous_id))
  have hDcont (x : E) : Continuous (fun y => D x y) := by
    exact hkc.smul (hdfcont.comp (continuous_const.sub continuous_id))
  have hFmeas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun y => k y • g (x - y)) (volume : Measure E) :=
    by filter_upwards with x; exact (hFcont x).aestronglyMeasurable
  have hFint : Integrable (fun y => k y • g (x₀ - y)) (volume : Measure E) := by
    exact (hFcont x₀).integrable_of_hasCompactSupport hk.smul_right
  have hDmeas : AEStronglyMeasurable (D x₀) (volume : Measure E) :=
    (hDcont x₀).aestronglyMeasurable
  have hkint : Integrable (fun y => ‖k y‖) (volume : Measure E) := by
    exact hkc.norm.integrable_of_hasCompactSupport hk.norm
  have hbound_int : Integrable (fun y => ‖k y‖ * C) (volume : Measure E) :=
    hkint.mul_const C
  have hDbound : ∀ᵐ y ∂(volume : Measure E), ∀ x ∈ Metric.ball x₀ 1,
      ‖D x y‖ ≤ ‖k y‖ * C := by
    filter_upwards with y
    intro x hx
    by_cases hy : y ∈ tsupport k
    · have hCx : ‖fderiv ℝ g (x - y)‖ ≤ C :=
        hbound x (Metric.mem_closedBall.mpr (by
          rw [dist_eq_norm]
          exact (mem_ball_iff_norm.mp hx).le)) y hy
      simp only [D, norm_smul]
      exact mul_le_mul_of_nonneg_left hCx (norm_nonneg _)
    · have hky : k y = 0 := by
        by_contra hne
        apply hy
        have hys : y ∈ Function.support k := by
          change k y ≠ 0
          exact hne
        exact subset_tsupport k hys
      simp [D, hky]
  have hdiff : ∀ᵐ y ∂(volume : Measure E), ∀ x ∈ Metric.ball x₀ 1,
      HasFDerivAt (fun x => k y • g (x - y)) (D x y) x := by
    filter_upwards with y x hx
    have hshift : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x := by
      simpa using (hasFDerivAt_id x).sub_const y
    have hcomp := (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp x hshift
    convert hcomp.const_smul (k y) using 1 <;> rfl
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds x₀ zero_lt_one) hFmeas hFint hDmeas hDbound hbound_int hdiff

private theorem convolution_parametric_hasFDerivAt_of_compact
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (k : E → ℝ) (hk : HasCompactSupport k) (hkc : Continuous k)
    (g : E → G) (hg : ContDiff ℝ 1 g) (x₀ : E) :
    HasFDerivAt (fun x => ∫ y, k y • g (x - y) ∂(volume : Measure E))
      (∫ y, k y • fderiv ℝ g (x₀ - y) ∂(volume : Measure E)) x₀ := by
  let K := (fun p : E × E => p.1 - p.2) '' (Metric.closedBall x₀ 1 ×ˢ tsupport k)
  have hK : IsCompact K := by
    exact (isCompact_closedBall x₀ 1).prod hk.isCompact |>.image
      (continuous_fst.sub continuous_snd)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  apply convolution_parametric_hasFDerivAt k hk hkc g hg x₀ C
  intro x hx y hy
  exact hC (x - y) ⟨(x, y), ⟨hx, hy⟩, rfl⟩

private theorem euclideanC2Convolution_order_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E} (A : EuclideanC2ConvolutionData E f U)
    (hf : ContDiff ℝ 2 f) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ 1 (A.approximation j) x =
      ∫ y, (A.kernel j).normed (volume : Measure E) y •
        iteratedFDeriv ℝ 1 f (x - y) ∂(volume : Measure E) := by
  let k := (A.kernel j).normed (volume : Measure E)
  have hk : HasCompactSupport k := (A.kernel j).hasCompactSupport_normed
  have hkc : Continuous k := (A.kernel j).continuous_normed
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hder := convolution_parametric_hasFDerivAt_of_compact k hk hkc f hf1 x
  have hEq : A.approximation j =
      fun z => ∫ y, k y • f (z - y) ∂(volume : Measure E) := by
    funext z
    rw [A.convolution_eq j]
    rw [convolution_lsmul]
  have hfd : fderiv ℝ (A.approximation j) x =
      ∫ y, k y • fderiv ℝ f (x - y) ∂(volume : Measure E) := by
    rw [hEq]
    exact hder.fderiv
  have hDcont : Continuous (fun y => k y • fderiv ℝ f (x - y)) := by
    exact hkc.smul (hf.continuous_fderiv (by norm_num) |>.comp
      (continuous_const.sub continuous_id))
  have hDint : Integrable (fun y => k y • fderiv ℝ f (x - y)) (volume : Measure E) :=
    hDcont.integrable_of_hasCompactSupport hk.smul_right
  have hjetcont : Continuous (fun y => k y • iteratedFDeriv ℝ 1 f (x - y)) := by
    exact hkc.smul (hf.continuous_iteratedFDeriv (by norm_num) |>.comp
      (continuous_const.sub continuous_id))
  have hjetint : Integrable (fun y => k y • iteratedFDeriv ℝ 1 f (x - y))
      (volume : Measure E) := hjetcont.integrable_of_hasCompactSupport hk.smul_right
  apply ContinuousMultilinearMap.ext
  intro m
  rw [iteratedFDeriv_one_apply, hfd, ContinuousLinearMap.integral_apply hDint,
    ContinuousMultilinearMap.integral_apply hjetint]
  simp [iteratedFDeriv_one_apply]

private theorem euclideanC2Convolution_order_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E} (A : EuclideanC2ConvolutionData E f U)
    (hf : ContDiff ℝ 2 f) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ 2 (A.approximation j) x =
      ∫ y, (A.kernel j).normed (volume : Measure E) y •
        iteratedFDeriv ℝ 2 f (x - y) ∂(volume : Measure E) := by
  let k := (A.kernel j).normed (volume : Measure E)
  have hk : HasCompactSupport k := (A.kernel j).hasCompactSupport_normed
  have hkc : Continuous k := (A.kernel j).continuous_normed
  let g := iteratedFDeriv ℝ 1 f
  have hg : ContDiff ℝ 1 g := hf.iteratedFDeriv_right'
  have hder := convolution_parametric_hasFDerivAt_of_compact k hk hkc g hg x
  have h1eq : iteratedFDeriv ℝ 1 (A.approximation j) =
      fun z => ∫ y, k y • iteratedFDeriv ℝ 1 f (z - y) ∂(volume : Measure E) := by
    funext z
    exact euclideanC2Convolution_order_one A hf j z
  have hfd : fderiv ℝ (iteratedFDeriv ℝ 1 (A.approximation j)) x =
      ∫ y, k y • fderiv ℝ g (x - y) ∂(volume : Measure E) := by
    rw [h1eq]
    exact hder.fderiv
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ
  rw [iteratedFDeriv_succ_eq_comp_left]
  change L.symm (fderiv ℝ (iteratedFDeriv ℝ 1 (A.approximation j)) x) = _
  rw [hfd]
  have hInt : Integrable (fun y : E => k y • fderiv ℝ g (x - y)) (volume : Measure E) := by
    have hcont : Continuous (fun y => k y • fderiv ℝ g (x - y)) := by
      exact hkc.smul ((hg.continuous_fderiv one_ne_zero).comp
        (continuous_const.sub continuous_id))
    exact hcont.integrable_of_hasCompactSupport hk.smul_right
  have hjetcont : Continuous (fun y => k y • iteratedFDeriv ℝ 2 f (x - y)) := by
    exact hkc.smul (hf.continuous_iteratedFDeriv (by norm_num) |>.comp
      (continuous_const.sub continuous_id))
  have hjetint : Integrable (fun y => k y • iteratedFDeriv ℝ 2 f (x - y))
      (volume : Measure E) := hjetcont.integrable_of_hasCompactSupport hk.smul_right
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.integral_apply hjetint m]
  simp only [L, continuousMultilinearCurryLeftEquiv_symm_apply]
  have hInt2 : Integrable (fun y => k y • fderiv ℝ g (x - y) (m 0))
      (volume : Measure E) := hInt.apply_continuousLinearMap (m 0)
  rw [ContinuousLinearMap.integral_apply hInt (m 0)]
  change (∫ y, k y • fderiv ℝ g (x - y) (m 0) ∂(volume : Measure E)) (Fin.tail m) = _
  rw [ContinuousMultilinearMap.integral_apply hInt2 (Fin.tail m)]
  apply integral_congr_ae
  filter_upwards with y
  change k y • fderiv ℝ (iteratedFDeriv ℝ 1 f) (x - y) (m 0) (Fin.tail m) =
    k y • iteratedFDeriv ℝ 2 f (x - y) m
  rw [← iteratedFDeriv_succ_apply_left]

/-- Classical differentiation under a compactly supported normalized convolution
through real order two. At order zero this also specifies the kernel's
orientation: the translated argument is `x - y`, not `y - x`. -/
theorem euclideanC2Convolution_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E}
    (A : EuclideanC2ConvolutionData E f U) (hf : ContDiff ℝ 2 f)
    (j : ℕ) (r : ℕ) (hr : r ≤ 2) (x : E) :
    iteratedFDeriv ℝ r (A.approximation j) x =
      ∫ y, ((A.kernel j).normed (volume : Measure E) y) •
        iteratedFDeriv ℝ r f (x - y) ∂(volume : Measure E) := by
  cases r with
  | zero => exact euclideanC2Convolution_zero_order A hf j x
  | succ r =>
    cases r with
    | zero => simpa using euclideanC2Convolution_order_one A hf j x
    | succ r =>
      cases r with
      | zero => simpa using euclideanC2Convolution_order_two A hf j x
      | succ r => omega
