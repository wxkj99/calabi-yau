module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.Mathlib.Geometry.Manifold.Holder

/-!
# Local fixed-chart bounds for forcing jets

Székelyhidi, §1.4, pp. 10–12, covariant derivative in coordinates;
§3.3, p. 45, differentiated-Ricci error. A C3 family bound controls the
Hessian and its first reference covariant derivative on compact subcharts.
Smoothness is separate from HolderBoundedInCharts: its derivative sup bounds
alone have junk values on nonsmooth functions.
-/

public section

open scoped Manifold ContDiff NNReal Topology Matrix.Norms.Elementwise MatrixOrder ComplexOrder
open Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

private theorem forcingChart_closedBall_subset_target (x : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  have hx : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := mem_extChartAt_target x
  have htarget : IsOpen (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    isOpen_extChartAt_target x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp htarget _ hx
  exact ⟨r / 2, by linarith,
    fun z hz => hball (Metric.mem_ball.mpr (lt_of_le_of_lt hz (by linarith)))⟩

private theorem exists_compact_chart_neighborhood_uniform_c3
    (F : Set (M → ℝ))
    (hHolder : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 F) (x : M) :
    ∃ K : Set (EuclideanSpace ℂ (Fin n)), IsCompact K ∧
      K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ∧
      ∃ C : ℝ≥0, (∀ G ∈ F,
        HolderBoundOn 3 0 C K
          (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) ∧
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∧
        ∀ y ∈ U, (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) ∈ K := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z₀ := c x
  obtain ⟨r, hr, hrTarget⟩ := forcingChart_closedBall_subset_target (n := n) x
  let K := Metric.closedBall z₀ r
  have hK : IsCompact K := isCompact_closedBall z₀ r
  have hKt : K ⊆ c.target := hrTarget
  obtain ⟨C, hC⟩ := hHolder x K hK hKt
  let U : Set M := c.source ∩ c ⁻¹' Metric.ball z₀ r
  refine ⟨K, hK, hKt, C, ?_, U, ?_, ?_, ?_, ?_⟩
  · intro G hG
    exact hC G hG
  · exact isOpen_extChartAt_preimage' x Metric.isOpen_ball
  · refine ⟨mem_extChartAt_source x, ?_⟩
    change c x ∈ Metric.ball z₀ r
    exact Metric.mem_ball_self hr
  · exact Set.inter_subset_left
  · intro y hy
    have hy' : c y ∈ Metric.ball z₀ r := hy.2
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy'))

section

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- A fixed chart near x supplies one finite coefficient, uniformly over the
forcing family and all frames normalized by the reference metric there. -/
private theorem forcing_det_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) :
    ContDiffAt ℝ ∞ (fun w => (A w).det) z := by
  have hentry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hA a) b
  have hpoly : ContDiffAt ℝ ∞
      (fun w => ∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ i, A w (σ i) i) z := by
    fun_prop (disch := assumption)
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w hw
  exact Matrix.det_apply (A w)

private theorem forcing_adjugate_entry_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (A w).adjugate i j) z := by
  have hentry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hA a) b
  have hpoly : ContDiffAt ℝ ∞
      (fun w => ((A w).updateRow j (Pi.single i 1)).det) z := by
    have hupdate (a b : Fin n) : ContDiffAt ℝ ∞
        (fun w => (A w).updateRow j (Pi.single i 1) a b) z := by
      by_cases ha : a = j
      · subst a
        simp only [Matrix.updateRow_apply]
        exact contDiffAt_const
      · simp only [Matrix.updateRow_apply, ite_eq_right ha]
        exact hentry a b
    have hmatrix : ContDiffAt ℝ ∞
        (fun w => (A w).updateRow j (Pi.single i 1)) z := by
      apply contDiffAt_pi.mpr
      intro a
      apply contDiffAt_pi.mpr
      intro b
      exact hupdate a b
    exact forcing_det_contDiffAt _ z hmatrix
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w hw
  exact Matrix.adjugate_apply (A w) i j

private theorem forcing_inverse_entry_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) (hunit : IsUnit (A z).det) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (A w)⁻¹ i j) z := by
  have hdet := forcing_det_contDiffAt A z hA
  have hinvdet : ContDiffAt ℝ ∞ (fun w => ((A w).det)⁻¹) z := by
    have hnz : (A z).det ≠ 0 := hunit.ne_zero
    exact (contDiffAt_inv ℝ hnz).comp z hdet
  have hadj := forcing_adjugate_entry_contDiffAt A z hA i j
  have hentry : ContDiffAt ℝ ∞
      (fun w => ((A w).det)⁻¹ * (A w).adjugate i j) z := hinvdet.mul hadj
  apply hentry.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w
  rw [Matrix.inv_def]
  simp [Matrix.smul_apply]

end

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem exists_fixed_chart_frame_entries_bounded
    (ω₀ : KahlerForm n M) (x : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ K, ∀ P : Matrix (Fin n) (Fin n) ℂ,
      P.transpose * ω₀.metricInChart x z * P.map star = 1 →
        ∀ i j, ‖P i j‖ ≤ Real.sqrt Q := by
  classical
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z => ω₀.metricInChart x z
  have hInvContinuous (i : Fin n) : ContinuousOn (fun z => ‖(g z)⁻¹ i i‖) K := by
    intro z hz
    have hgEntry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z := by
      exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (hKt hz))
    have hg : ContDiffAt ℝ ∞ g z := by
      apply contDiffAt_pi.mpr
      intro a
      apply contDiffAt_pi.mpr
      intro b
      exact hgEntry a b
    have hdet : IsUnit (g z).det :=
      (Matrix.isUnit_iff_isUnit_det (g z)).mp (ω₀.posDef_metricInChart x (hKt hz)).isUnit
    have hinv : ContDiffAt ℝ ∞ (fun w => (g w)⁻¹) z := by
      apply contDiffAt_pi.mpr
      intro a
      apply contDiffAt_pi.mpr
      intro b
      exact forcing_inverse_entry_contDiffAt g z hg hdet a b
    exact (continuous_norm.continuousAt.comp
      (contDiffAt_pi.mp (contDiffAt_pi.mp hinv i) i).continuousAt).continuousWithinAt
  have hBound (i : Fin n) : ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ K, ‖(g z)⁻¹ i i‖ ≤ D := by
    let f : EuclideanSpace ℂ (Fin n) → ℝ := fun z => ‖(g z)⁻¹ i i‖
    have hbdd : BddAbove (f '' K) := hK.bddAbove_image (hInvContinuous i)
    obtain ⟨D, hD⟩ := hbdd
    refine ⟨max 0 D, le_max_left _ _, ?_⟩
    intro z hz
    exact (hD (Set.mem_image_of_mem f hz)).trans (le_max_right _ _)
  let D : Fin n → ℝ := fun i => Classical.choose (hBound i)
  have hDnonneg (i : Fin n) : 0 ≤ D i := (Classical.choose_spec (hBound i)).1
  have hDbound (i : Fin n) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      ‖(g z)⁻¹ i i‖ ≤ D i := (Classical.choose_spec (hBound i)).2 z hz
  let Q : ℝ := ∑ i, D i + 1
  refine ⟨Q, ?_, ?_⟩
  · dsimp [Q]
    exact add_nonneg (Finset.sum_nonneg (fun i hi => hDnonneg i)) (by norm_num)
  · intro z hz P hP i j
    have h' : (P.transpose * g z) * P.map star = 1 := by
      simpa [Matrix.mul_assoc] using hP
    have hleft : P.map star * (P.transpose * g z) = 1 := mul_eq_one_comm.1 h'
    have hleft' : (P.map star * P.transpose) * g z = 1 := by
      simpa [Matrix.mul_assoc] using hleft
    have hAinv : (g z)⁻¹ = P.map star * P.transpose := Matrix.inv_eq_left_inv hleft'
    have hsum : ∑ a : Fin n, Complex.normSq (P i a) = ((g z)⁻¹ i i).re := by
      have hmat := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X i i) hAinv
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply] at hmat
      have hre := congrArg Complex.re hmat
      rw [Complex.re_sum] at hre
      have hterm (w : ℂ) : (star w * w).re = Complex.normSq w := by
        have hh := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := w))
        simpa using hh.symm
      simp_rw [hterm] at hre
      exact hre.symm
    have hsumEntry : Complex.normSq (P i j) ≤ ∑ a : Fin n, Complex.normSq (P i a) :=
      Finset.single_le_sum (fun a ha => Complex.normSq_nonneg _) (Finset.mem_univ j)
    have hdiagBound : ((g z)⁻¹ i i).re ≤ Q := by
      have habs := hDbound i z hz
      have hre := (Complex.abs_re_le_norm ((g z)⁻¹ i i)).trans habs
      dsimp [Q]
      have hsingle : D i ≤ ∑ a, D a :=
        Finset.single_le_sum (fun a ha => hDnonneg a) (Finset.mem_univ i)
      linarith [le_abs_self (((g z)⁻¹ i i).re)]
    have hsq : ‖P i j‖ ^ 2 ≤ Q := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hsumEntry.trans (hsum ▸ hdiagBound)
    have hsqrt : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ Q by
      dsimp [Q]
      exact add_nonneg (Finset.sum_nonneg (fun a ha => hDnonneg a)) (by norm_num))]

section

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem forcing_twoFrame_bound {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (Q : Fin n → Fin n → ℂ) (B C : ℝ)
    (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hP : ∀ i j, ‖P i j‖ ≤ B) (hQ : ∀ i j, ‖Q i j‖ ≤ C)
    (j l : Fin n) :
    ‖c3TwoCovariantFrame P Q j l‖ ≤ (n : ℝ) ^ 2 * B ^ 2 * C := by
  unfold c3TwoCovariantFrame
  calc
    ‖∑ a, ∑ b, P a j * star (P b l) * Q a b‖ ≤
        ∑ a, ∑ b, ‖P a j * star (P b l) * Q a b‖ := by
      calc
        ‖∑ a, ∑ b, _‖ ≤ ∑ a, ‖∑ b, _‖ := norm_sum_le _ _
        _ ≤ ∑ a, ∑ b, ‖P a j * star (P b l) * Q a b‖ :=
          Finset.sum_le_sum fun a ha => norm_sum_le _ _
    _ = ∑ a, ∑ b, ‖P a j‖ * ‖P b l‖ * ‖Q a b‖ := by simp
    _ ≤ ∑ a, ∑ b, B * B * C := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have hPa := hP a j
      have hPb := hP b l
      have hQab := hQ a b
      have hPa0 := norm_nonneg (P a j)
      have hPb0 := norm_nonneg (P b l)
      have hQab0 := norm_nonneg (Q a b)
      calc
        ‖P a j‖ * ‖P b l‖ * ‖Q a b‖ ≤ B * B * ‖Q a b‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hPa hPb hPb0 hB) hQab0
        _ ≤ B * B * C := by
          exact mul_le_mul_of_nonneg_left hQab (mul_nonneg hB hB)
    _ = (n : ℝ) ^ 2 * B ^ 2 * C := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

private theorem forcing_threeFrame_bound {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin n → Fin n → Fin n → ℂ) (B C : ℝ)
    (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hP : ∀ i j, ‖P i j‖ ≤ B) (hD : ∀ i j k, ‖D i j k‖ ≤ C)
    (k j l : Fin n) :
    ‖c3ThreeCovariantFrame P D k j l‖ ≤ (n : ℝ) ^ 3 * B ^ 3 * C := by
  unfold c3ThreeCovariantFrame
  calc
    ‖∑ a, ∑ b, ∑ c, P a k * P b j * star (P c l) * D a b c‖ ≤
        ∑ a, ∑ b, ∑ c, ‖P a k * P b j * star (P c l) * D a b c‖ := by
      calc
        ‖∑ a, ∑ b, ∑ c, _‖ ≤ ∑ a, ‖∑ b, ∑ c, _‖ := norm_sum_le _ _
        _ ≤ ∑ a, ∑ b, ‖∑ c, _‖ := by
          apply Finset.sum_le_sum
          intro a ha
          exact norm_sum_le _ _
        _ ≤ ∑ a, ∑ b, ∑ c, ‖P a k * P b j * star (P c l) * D a b c‖ := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          exact norm_sum_le _ _
    _ = ∑ a, ∑ b, ∑ c,
        ‖P a k‖ * ‖P b j‖ * ‖P c l‖ * ‖D a b c‖ := by simp
    _ ≤ ∑ a, ∑ b, ∑ c, B * B * B * C := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      have hPa := hP a k
      have hPb := hP b j
      have hPc := hP c l
      have hDabc := hD a b c
      have hPb0 := norm_nonneg (P b j)
      have hPc0 := norm_nonneg (P c l)
      have hD0 := norm_nonneg (D a b c)
      have hAB : ‖P a k‖ * ‖P b j‖ ≤ B * B := mul_le_mul hPa hPb hPb0 hB
      have hABC : ‖P a k‖ * ‖P b j‖ * ‖P c l‖ ≤ B * B * B := by
        calc
          ‖P a k‖ * ‖P b j‖ * ‖P c l‖ ≤ B * B * ‖P c l‖ :=
            mul_le_mul_of_nonneg_right hAB hPc0
          _ ≤ B * B * B := mul_le_mul_of_nonneg_left hPc (mul_nonneg hB hB)
      calc
        ‖P a k‖ * ‖P b j‖ * ‖P c l‖ * ‖D a b c‖ ≤ B * B * B * ‖D a b c‖ :=
          mul_le_mul_of_nonneg_right hABC hD0
        _ ≤ B * B * B * C := mul_le_mul_of_nonneg_left hDabc (by positivity)
    _ = (n : ℝ) ^ 3 * B ^ 3 * C := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

private noncomputable def hessianEntryEval {n : ℕ}
    (v w : EuclideanSpace ℂ (Fin n)) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) v)

private noncomputable def hessianEntryQ {n : ℕ} (i j : Fin n) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let w : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iv := Complex.I • v
  let iw := Complex.I • w
  let e₁ := hessianEntryEval v w
  let e₂ := hessianEntryEval iv iw
  let e₃ := hessianEntryEval v iw
  let e₄ := hessianEntryEval iv w
  let realPart
      (e : (EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ) :
      (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp e
  exact (1 / 4 : ℝ) • (realPart e₁ + realPart e₂ +
    (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (realPart (e₃ - e₄)))

private theorem hessian_eq_Q {n : ℕ} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hu : ContDiffAt ℝ 2 u z) (i j : Fin n) :
    complexHessian u z i j = hessianEntryQ i j (fderiv ℝ (fderiv ℝ u) z) := by
  rw [complexHessian_apply hu]
  simp [hessianEntryQ, hessianEntryEval]
  ring_nf

private theorem hessianQ_norm_le {n : ℕ} (i j : Fin n) :
    ‖hessianEntryQ i j‖ ≤ 1 := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let w : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iv := Complex.I • v
  let iw := Complex.I • w
  have hv : ‖v‖ = 1 := by simp [v]
  have hw : ‖w‖ = 1 := by simp [w]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hiw : ‖iw‖ = 1 := by simp [iw, hw, norm_smul, Complex.norm_I]
  have hEval (a b : EuclideanSpace ℂ (Fin n)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (T : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
      ‖T a b‖ ≤ ‖T‖ := by
    calc
      ‖T a b‖ ≤ ‖T a‖ * ‖b‖ := (T a).le_opNorm b
      _ ≤ ‖T‖ * ‖a‖ * ‖b‖ := by gcongr; exact T.le_opNorm a
      _ = ‖T‖ := by rw [ha, hb]; ring
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  dsimp [hessianEntryQ]
  have h1 : ‖Complex.ofReal (T v w)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval v w hv hw T
  have h2 : ‖Complex.ofReal (T iv iw)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval iv iw hiv hiw T
  have h3 : ‖Complex.ofReal (T v iw)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval v iw hv hiw T
  have h4 : ‖Complex.ofReal (T iv w)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval iv w hiv hw T
  have hrest : ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤
      ‖T‖ + ‖T‖ := by
    rw [norm_mul, Complex.norm_I]
    simpa only [one_mul] using (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hnum : ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw) +
      Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤ 4 * ‖T‖ := by
    calc
      _ ≤ ‖Complex.ofReal (T v w)‖ + ‖Complex.ofReal (T iv iw)‖ +
          ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ := by
        calc
          _ ≤ ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw)‖ +
              ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ 4 * ‖T‖ := by nlinarith
  rw [one_mul]
  rw [_root_.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hscaled : (1 / 4) *
      ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw) +
        Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤ ‖T‖ := by
    calc
      (1 / 4) * _ ≤ (1 / 4) * (4 * ‖T‖) := mul_le_mul_of_nonneg_left hnum (by norm_num)
      _ = ‖T‖ := by ring
  simpa [hessianEntryEval, v, w, iv, iw, mul_sub] using hscaled

private theorem hessian_entry_norm_le_jet
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (h : ContDiffAt ℝ 2 f z) (i j : Fin n) :
    ‖complexHessian f z i j‖ ≤ ‖iteratedFDeriv ℝ 2 f z‖ := by
  rw [hessian_eq_Q h i j]
  calc
    ‖hessianEntryQ i j (fderiv ℝ (fderiv ℝ f) z)‖ ≤
        ‖hessianEntryQ i j‖ * ‖fderiv ℝ (fderiv ℝ f) z‖ :=
      (hessianEntryQ i j).le_opNorm _
    _ ≤ 1 * ‖iteratedFDeriv ℝ 2 f z‖ := by
      have hjet : ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
        calc
          ‖fderiv ℝ (fderiv ℝ f) z‖ =
              ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ f)) z‖ := by simp
          _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) z‖ := by
            simpa only [iteratedFDeriv_zero] using
              (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ f) (x := z) (n := 0))
          _ = ‖iteratedFDeriv ℝ 2 f z‖ :=
            norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := z) (n := 1)
      rw [hjet]
      exact mul_le_mul_of_nonneg_right (hessianQ_norm_le i j) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ 2 f z‖ := by ring

private theorem hessian_entry_first_jet_bound
    {n : ℕ} {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hVU : V ⊆ U)
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (huCont : ContDiffOn ℝ 3 u U) (i j : Fin n) :
    ∀ z ∈ V,
      ‖iteratedFDeriv ℝ 1 (fun y ↦ complexHessian u y i j) z‖ ≤
        ‖iteratedFDeriv ℝ 3 u z‖ := by
  intro z hz
  let g : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
    fun y ↦ fderiv ℝ (fderiv ℝ u) y
  have hDu : ContDiffOn ℝ 2 (fderiv ℝ u) U :=
    huCont.fderiv_of_isOpen hU (by norm_num)
  have hg : ContDiffOn ℝ 1 g U := hDu.fderiv_of_isOpen hU (by norm_num)
  have hSmoothAt (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ U) :
      ContDiffAt ℝ 2 u y := (huCont y hy).contDiffAt (hU.mem_nhds hy) |>.of_le (by norm_num)
  have hEq : (fun y ↦ complexHessian u y i j) =ᶠ[𝓝 z]
      (hessianEntryQ i j ∘ g) := by
    filter_upwards [hU.mem_nhds (hVU hz)] with y hy
    exact hessian_eq_Q (hSmoothAt y hy) i j
  have hJet : iteratedFDeriv ℝ 1 (fun y ↦ complexHessian u y i j) z =
      (hessianEntryQ i j).compContinuousMultilinearMap (iteratedFDeriv ℝ 1 g z) := by
    calc
      iteratedFDeriv ℝ 1 (fun y ↦ complexHessian u y i j) z =
          iteratedFDeriv ℝ 1 (hessianEntryQ i j ∘ g) z :=
            (hEq.iteratedFDeriv ℝ 1).eq_of_nhds
      _ = (hessianEntryQ i j).compContinuousMultilinearMap (iteratedFDeriv ℝ 1 g z) :=
        (hessianEntryQ i j).iteratedFDeriv_comp_left
          ((hg z (hVU hz)).contDiffAt (hU.mem_nhds (hVU hz))) (by norm_num)
  have hjetNorm : ‖iteratedFDeriv ℝ 1 g z‖ = ‖iteratedFDeriv ℝ 3 u z‖ := by
    dsimp [g]
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  rw [hJet]
  calc
    ‖(hessianEntryQ i j).compContinuousMultilinearMap (iteratedFDeriv ℝ 1 g z)‖ ≤
        ‖hessianEntryQ i j‖ * ‖iteratedFDeriv ℝ 1 g z‖ :=
      (hessianEntryQ i j).norm_compContinuousMultilinearMap_le _
    _ ≤ 1 * ‖iteratedFDeriv ℝ 3 u z‖ := by rw [hjetNorm]; gcongr; exact hessianQ_norm_le i j
    _ = ‖iteratedFDeriv ℝ 3 u z‖ := by ring

private theorem partialZ_norm_le_fderiv
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (k : Fin n) : ‖wirtingerDerivInChart f z k‖ ≤ ‖fderiv ℝ f z‖ := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hiv : ‖Complex.I • v‖ = 1 := by simp [hv, norm_smul, Complex.norm_I]
  have h1 : ‖fderiv ℝ f z v‖ ≤ ‖fderiv ℝ f z‖ := by
    calc
      ‖fderiv ℝ f z v‖ ≤ ‖fderiv ℝ f z‖ * ‖v‖ := (fderiv ℝ f z).le_opNorm v
      _ = ‖fderiv ℝ f z‖ := by rw [hv]; ring
  have h2 : ‖fderiv ℝ f z (Complex.I • v)‖ ≤ ‖fderiv ℝ f z‖ := by
    calc
      ‖fderiv ℝ f z (Complex.I • v)‖ ≤ ‖fderiv ℝ f z‖ * ‖Complex.I • v‖ :=
        (fderiv ℝ f z).le_opNorm (Complex.I • v)
      _ = ‖fderiv ℝ f z‖ := by rw [hiv]; ring
  change ‖(fderiv ℝ f z v - Complex.I * fderiv ℝ f z (Complex.I • v)) / 2‖ ≤ _
  rw [norm_div]
  have hI : ‖Complex.I * fderiv ℝ f z (Complex.I • v)‖ =
      ‖fderiv ℝ f z (Complex.I • v)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hnum : ‖fderiv ℝ f z v - Complex.I * fderiv ℝ f z (Complex.I • v)‖ ≤
      ‖fderiv ℝ f z‖ + ‖fderiv ℝ f z‖ := by
    calc
      _ ≤ ‖fderiv ℝ f z v‖ + ‖Complex.I * fderiv ℝ f z (Complex.I • v)‖ := norm_sub_le _ _
      _ = ‖fderiv ℝ f z v‖ + ‖fderiv ℝ f z (Complex.I • v)‖ := by rw [hI]
      _ ≤ ‖fderiv ℝ f z‖ + ‖fderiv ℝ f z‖ := add_le_add h1 h2
  simpa using (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    (by nlinarith [norm_nonneg (fderiv ℝ f z)])

end

section

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem exists_local_background_christoffel_bound
    (ω₀ : KahlerForm n M) (x₀ : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ∀ i j k : Fin n,
      ‖christoffelInChart (ω₀.metricInChart x₀) z i j k‖ ≤ R := by
  classical
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target
  let g := fun z => ω₀.metricInChart x₀ z
  have hU : IsOpen U := isOpen_extChartAt_target x₀
  have hgCont : ContinuousOn g U := by
    apply continuousOn_pi.mpr
    intro a
    apply continuousOn_pi.mpr
    intro b
    exact (ω₀.contDiffOn_metricInChart x₀ a b).continuousOn
  have hinv (l i : Fin n) : ContinuousOn (fun z => (g z)⁻¹ l i) U := by
    intro z hz
    have hG : ContinuousAt g z := (hgCont z hz).continuousAt (hU.mem_nhds hz)
    have hunit : IsUnit (g z).det :=
      (Matrix.isUnit_iff_isUnit_det (g z)).mp (ω₀.posDef_metricInChart x₀ hz).isUnit
    have hdet : (g z).det ≠ 0 := hunit.ne_zero
    have hdetAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) (g z) := by
      fun_prop
    have hAdjAt : ContinuousAt
        (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate) (g z) := by
      fun_prop
    have hinvDetAt : ContinuousAt
        (fun A : Matrix (Fin n) (Fin n) ℂ => Ring.inverse A.det) (g z) := by
      have hscalar : ContinuousAt (fun w : ℂ => Ring.inverse w) (g z).det := by
        simpa only [Ring.inverse_eq_inv] using continuousAt_inv₀ hdet
      exact hscalar.comp hdetAt
    have hinvMatrix : ContinuousAt
        (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) (g z) := by
      change ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ =>
        Ring.inverse A.det • A.adjugate) (g z)
      exact hinvDetAt.smul hAdjAt
    have hinvMatrixAt : ContinuousAt (fun w => (g w)⁻¹) z := hinvMatrix.comp hG
    have hinvEntry : ContinuousAt (fun w => (g w)⁻¹ l i) z := by
      have h₁ := continuousAt_pi.mp hinvMatrixAt l
      exact continuousAt_pi.mp h₁ i
    exact hinvEntry.continuousWithinAt
  have hderiv (k l j : Fin n) (v : EuclideanSpace ℂ (Fin n)) :
      ContinuousOn (fun z => fderiv ℝ (fun w => g w k l) z v) U := by
    intro z hz
    have hF : ContDiffAt ℝ ∞ (fun w => g w k l) z :=
      (ω₀.contDiffOn_metricInChart x₀ k l).contDiffAt (hU.mem_nhds hz)
    have hfd : ContDiffAt ℝ ∞ (fun w => fderiv ℝ (fun v => g v k l) w) z :=
      hF.fderiv_right (m := ∞)
        (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)
    have hcont : ContinuousAt (fun w => fderiv ℝ (fun v => g v k l) w v) z := by
      fun_prop (disch := assumption)
    exact hcont.continuousWithinAt
  have hpartial (j k l : Fin n) : ContinuousOn
      (fun z => wirtingerDerivInChart (fun w => g w k l) z j) U := by
    have h₁ := hderiv k l j (EuclideanSpace.single j 1)
    have h₂ := hderiv k l j (Complex.I • EuclideanSpace.single j 1)
    simpa [wirtingerDerivInChart] using h₁.sub (continuousOn_const.mul h₂) |>.div_const 2
  have hγ (i j k : Fin n) : ContinuousOn
      (fun z => ‖christoffelInChart g z i j k‖) U := by
    have hterm (l : Fin n) : ContinuousOn
        (fun z => (g z)⁻¹ l i * wirtingerDerivInChart (fun w => g w k l) z j) U :=
      (hinv l i).mul (hpartial j k l)
    have hsum : ContinuousOn
        (fun z => ∑ l : Fin n,
          (g z)⁻¹ l i * wirtingerDerivInChart (fun w => g w k l) z j) U :=
      continuousOn_finsetSum Finset.univ (fun l hl => hterm l)
    simpa [christoffelInChart] using hsum.norm
  choose B hB0 hB using fun i j k =>
    (hK.bddAbove_image ((hγ i j k).mono hKt)).exists_ge 0
  refine ⟨∑ i, ∑ j, ∑ k, B i j k, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj =>
      Finset.sum_nonneg (fun k hk => hB0 i j k)))
  · intro z hz i j k
    have hval : ‖christoffelInChart g z i j k‖ ≤ B i j k :=
      hB i j k _ (Set.mem_image_of_mem _ hz)
    calc
      ‖christoffelInChart g z i j k‖ ≤ B i j k := hval
      _ ≤ ∑ a, ∑ b, ∑ c, B a b c := by
        apply le_trans (Finset.single_le_sum (fun c hc => hB0 i j c) (Finset.mem_univ k))
        apply le_trans (Finset.single_le_sum (fun b hb =>
          Finset.sum_nonneg (fun c hc => hB0 i b c)) (Finset.mem_univ j))
        exact Finset.single_le_sum (fun a ha => Finset.sum_nonneg (fun b hb =>
          Finset.sum_nonneg (fun c hc => hB0 a b c))) (Finset.mem_univ i)

theorem exists_local_c3ForcingFrameBound (ω₀ : KahlerForm n M)
    (F : Set (M → ℝ))
    (hF : ∀ G ∈ F, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hHolder : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 F) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ G ∈ F, ∀ y ∈ U, ∀ P : Matrix (Fin n) (Fin n) ℂ,
        P.transpose * ω₀.metricInChart x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) * P.map star = 1 →
          ForcingFrameBound ω₀ G x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) P A := by
  obtain ⟨K, hK, hKt, C, hC, U, hUopen, hUx, hUs, hUK⟩ :=
    exists_compact_chart_neighborhood_uniform_c3 F hHolder x
  obtain ⟨R, hR0, hR⟩ := exists_local_background_christoffel_bound ω₀ x K hK hKt
  obtain ⟨Q, hQ0, hQ⟩ := exists_fixed_chart_frame_entries_bounded ω₀ x K hK hKt
  let B : ℝ := Real.sqrt Q
  let A : ℝ := max ((n : ℝ) ^ 2 * B ^ 2 * (C : ℝ))
    ((n : ℝ) ^ 3 * B ^ 3 * ((C : ℝ) + (n : ℝ) * R * (C : ℝ)))
  refine ⟨U, hUopen, hUx, hUs, A, ?_, ?_⟩
  · dsimp [A, B]
    positivity
  · intro G hG y hy P hP
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let u : EuclideanSpace ℂ (Fin n) → ℝ := G ∘ c.symm
    have huCont : ContDiffOn ℝ ∞ u c.target := by
      have h := (contMDiff_iff.mp (hF G hG)).2 x 0
      simpa [u, c, extChartAt, chartAt_self_eq] using h
    have htargetOpen : IsOpen c.target := isOpen_extChartAt_target x
    have h3top : (3 : ℕ∞ω) ≤ ∞ := by simp
    have h2top : (2 : ℕ∞ω) ≤ ∞ := by simp
    have huCont3 : ContDiffOn ℝ 3 u c.target := huCont.of_le h3top
    have hAt (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
        ContDiffAt ℝ 2 u z :=
      (huCont z (hKt hz)).contDiffAt (htargetOpen.mem_nhds (hKt hz)) |>.of_le h2top
    have hHess (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) (i j : Fin n) :
        ‖c3ForcingHessianInChart G x z i j‖ ≤ (C : ℝ) := by
      change ‖complexHessian u z i j‖ ≤ (C : ℝ)
      exact (hessian_entry_norm_le_jet u z (hAt z hz) i j).trans
        ((hC G hG).1 2 (by norm_num) z hz)
    have hHessDeriv (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) (i j : Fin n) :
        ‖iteratedFDeriv ℝ 1 (fun w => complexHessian u w i j) z‖ ≤
          ‖iteratedFDeriv ℝ 3 u z‖ :=
      hessian_entry_first_jet_bound htargetOpen hKt huCont3 i j z hz
    have hCov (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K)
        (k j l : Fin n) :
        ‖c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x)
          z k j l‖ ≤ (C : ℝ) + (n : ℝ) * R * (C : ℝ) := by
      have hfirstEq : ‖fderiv ℝ (fun w => complexHessian u w j l) z‖ =
          ‖iteratedFDeriv ℝ 1 (fun w => complexHessian u w j l) z‖ := by
        calc
          ‖fderiv ℝ (fun w => complexHessian u w j l) z‖ =
              ‖iteratedFDeriv ℝ 0
                (fderiv ℝ (fun w => complexHessian u w j l)) z‖ := by simp
          _ = ‖iteratedFDeriv ℝ 1 (fun w => complexHessian u w j l) z‖ := by
            simpa only [iteratedFDeriv_zero] using
              (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
                (f := fun w => complexHessian u w j l) (x := z) (n := 0))
      have hfirst : ‖fderiv ℝ (fun w => complexHessian u w j l) z‖ ≤
          ‖iteratedFDeriv ℝ 1 (fun w => complexHessian u w j l) z‖ := le_of_eq hfirstEq
      have hpartial : ‖wirtingerDerivInChart (fun w => complexHessian u w j l) z k‖ ≤
          (C : ℝ) := by
        calc
          ‖wirtingerDerivInChart (fun w => complexHessian u w j l) z k‖ ≤
              ‖fderiv ℝ (fun w => complexHessian u w j l) z‖ :=
            partialZ_norm_le_fderiv _ _ _
          _ ≤ ‖iteratedFDeriv ℝ 1
              (fun w => complexHessian u w j l) z‖ := hfirst
          _ ≤ ‖iteratedFDeriv ℝ 3 u z‖ := hHessDeriv z hz j l
          _ ≤ (C : ℝ) := (hC G hG).1 3 (by norm_num) z hz
      have hcorrection :
          ‖∑ r, christoffelInChart (ω₀.metricInChart x) z r k j *
              c3ForcingHessianInChart G x z r l‖ ≤ (n : ℝ) * R * (C : ℝ) := by
        calc
          ‖∑ r, christoffelInChart (ω₀.metricInChart x) z r k j *
              c3ForcingHessianInChart G x z r l‖ ≤
              ∑ r, ‖christoffelInChart (ω₀.metricInChart x) z r k j *
                c3ForcingHessianInChart G x z r l‖ := norm_sum_le _ _
          _ ≤ ∑ r, R * (C : ℝ) := by
            apply Finset.sum_le_sum
            intro r hr
            rw [norm_mul]
            exact mul_le_mul (hR z hz r k j) (hHess z hz r l)
              (norm_nonneg _) hR0
          _ = (n : ℝ) * R * (C : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
      change ‖wirtingerDerivInChart (fun w => complexHessian u w j l) z k -
          ∑ r, christoffelInChart (ω₀.metricInChart x) z r k j *
            c3ForcingHessianInChart G x z r l‖ ≤ _
      calc
        _ ≤ ‖wirtingerDerivInChart (fun w => complexHessian u w j l) z k‖ +
            ‖∑ r, christoffelInChart (ω₀.metricInChart x) z r k j *
              c3ForcingHessianInChart G x z r l‖ := norm_sub_le _ _
        _ ≤ (C : ℝ) + (n : ℝ) * R * (C : ℝ) := add_le_add hpartial hcorrection
    have hzK : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) ∈ K := hUK y hy
    have hPB : ∀ i j, ‖P i j‖ ≤ B := by
      intro i j
      exact hQ _ hzK P hP i j
    have htwo := forcing_twoFrame_bound
      (P := P) (Q := c3ForcingHessianInChart G x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
      (B := B) (C := (C : ℝ)) (hB := Real.sqrt_nonneg Q)
      (_hC := C.property) (hP := hPB) (hQ := hHess _ hzK)
    have hthree := forcing_threeFrame_bound
      (P := P) (D := c3ReferenceCovariantTwoTensorZ ω₀ x
        (c3ForcingHessianInChart G x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
      (B := B) (C := (C : ℝ) + (n : ℝ) * R * (C : ℝ))
      (hB := Real.sqrt_nonneg Q) (_hC := by positivity)
      (hP := hPB) (hD := hCov _ hzK)
    refine ⟨?_, ?_⟩
    · intro j l
      exact (htwo j l).trans (le_max_left _ _)
    · intro k j l
      exact (hthree k j l).trans (le_max_right _ _)

end

end KahlerForm
