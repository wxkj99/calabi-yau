module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.Basic

/-!
# Local curvature bound in one holomorphic chart

On a relatively compact neighborhood of `x` inside its coordinate chart, the smooth metric
has a uniformly nondegenerate inverse, its curvature components are bounded, and its unitary
frames are bounded.  This is a *fixed-chart* estimate: unlike arbitrary coordinate components,
there is no varying coordinate rescaling in the assertion.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem fixedChartClosedBall_subset_target (x : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) r ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  have hx : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    exact mem_extChartAt_target x
  have htarget : IsOpen (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    isOpen_extChartAt_target x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp htarget _ hx
  exact ⟨r / 2, by linarith,
    fun z hz => hball (Metric.mem_ball.mpr (lt_of_le_of_lt hz (by linarith)))⟩

private theorem fixedChartPartialZ_contDiffAt
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    ContDiffAt ℝ ∞ (fun w => chartPartialZComplex F w p) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialZComplex
  fun_prop (disch := assumption)

private theorem fixedChartCurvature_continuousAt
    {n : ℕ} (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hdet : IsUnit (g z).det) (p q j k : Fin n) :
    ContinuousAt (fun w => chartCurvature g w p q j k) z := by
  have hInv (a b : Fin n) : ContinuousAt (fun w => (g w)⁻¹ a b) z :=
    (chartInv_differentiableAt (fun i j => (hg i j).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) a b).continuousAt
  have hDeriv (a b : Fin n) :
      ContDiffAt ℝ ∞ (fun w => fderiv ℝ (fun v => g v a b) w) z :=
    (hg a b).fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)
  have hZ (a b r : Fin n) :
      ContinuousAt (fun w => chartPartialZComplex (fun v => g v a b) w r) z := by
    unfold chartPartialZComplex
    fun_prop (disch := assumption)
  have hBar (a b r : Fin n) :
      ContDiffAt ℝ ∞ (fun w => chartPartialBarComplex (fun v => g v a b) w r) z := by
    unfold chartPartialBarComplex
    fun_prop (disch := assumption)
  have hZBar (a b r s : Fin n) :
      ContinuousAt (fun w => chartPartialZComplex
        (fun v => chartPartialBarComplex (fun t => g t a b) v s) w r) z :=
    (fixedChartPartialZ_contDiffAt _ z (hBar a b s) r).continuousAt
  unfold chartCurvature
  fun_prop (disch := assumption)

private theorem fixedChart_frame_entry_bound
    {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℂ)
    (h : P.transpose * A * P.map star = 1) (i j : Fin n) :
    ‖P i j‖ ≤ ‖A⁻¹ i i‖ + 1 := by
  have h' : (P.transpose * A) * P.map star = 1 := by
    simpa [Matrix.mul_assoc] using h
  have hleft : P.map star * (P.transpose * A) = 1 := mul_eq_one_comm.1 h'
  have hleft' : (P.map star * P.transpose) * A = 1 := by
    simpa [Matrix.mul_assoc] using hleft
  have hInv : A⁻¹ = P.map star * Matrix.transpose P := Matrix.inv_eq_left_inv hleft'
  have hdiag : ∑ a, Complex.normSq (P i a) = (A⁻¹ i i).re := by
    have hmat := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X i i) hInv
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply] at hmat
    have hre := congrArg Complex.re hmat
    rw [Complex.re_sum] at hre
    have hterm (z : ℂ) : (star z * z).re = Complex.normSq z := by
      have hh := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))
      simpa using hh.symm
    simp_rw [hterm] at hre
    exact hre.symm
  have hsum : Complex.normSq (P i j) ≤ ∑ a, Complex.normSq (P i a) :=
    Finset.single_le_sum (fun a ha => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have hdiagBound : (A⁻¹ i i).re ≤ ‖A⁻¹ i i‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsq : ‖P i j‖ ^ 2 ≤ ‖A⁻¹ i i‖ := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (hsum.trans_eq hdiag).trans hdiagBound
  have hnonneg : 0 ≤ ‖P i j‖ := norm_nonneg _
  nlinarith

private theorem fixedChart_compact_contraction_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, z ∈ K → ∀ (P : Matrix (Fin n) (Fin n) ℂ),
      P.transpose * ω₀.metricInChart x z * P.map star = 1 → ∀ p q j k,
      ‖∑ a, ∑ b, ∑ c, ∑ d,
          P a p * star (P b q) * P c j * star (P d k) *
            chartCurvature (fun w => ω₀.metricInChart x w) z a b c d‖ ≤ B := by
  classical
  let g := fun w => ω₀.metricInChart x w
  let T := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  have hT : IsOpen T := isOpen_extChartAt_target x
  have hgAt (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) (a b : Fin n) :
      ContDiffAt ℝ ∞ (fun w => g w a b) z :=
    (ω₀.contDiffOn_metricInChart x a b).contDiffAt (hT.mem_nhds (hKt hz))
  have hdet (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) : IsUnit (g z).det :=
    (Matrix.isUnit_iff_isUnit_det (g z)).mp (ω₀.posDef_metricInChart x (hKt hz)).isUnit
  have hCompactUpperBound (f : EuclideanSpace ℂ (Fin n) → ℝ)
      (hf : ContinuousOn f K) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, f z ≤ C := by
    have hbdd : BddAbove (f '' K) := hK.bddAbove_image hf
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro z hz
    exact (hC (Set.mem_image_of_mem f hz)).trans (le_max_right _ _)
  have hCurvCont (a b c d : Fin n) :
      ContinuousOn (fun z => chartCurvature g z a b c d) K := by
    intro z hz
    exact (fixedChartCurvature_continuousAt g z (hgAt z hz) (hdet z hz) a b c d).continuousWithinAt
  have hCurvBound (a b c d : Fin n) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖chartCurvature g z a b c d‖ ≤ C := by
    let f := fun z => ‖chartCurvature g z a b c d‖
    have hf : ContinuousOn f K := (continuous_norm.comp_continuousOn (hCurvCont a b c d))
    exact hCompactUpperBound f hf
  have hInvCont (i : Fin n) : ContinuousOn (fun z => ‖(g z)⁻¹ i i‖) K := by
    intro z hz
    have hi : DifferentiableAt ℝ (fun w => (g w)⁻¹ i i) z :=
      chartInv_differentiableAt (fun a b => (hgAt z hz a b).of_le (by norm_num))
        ((Matrix.isUnit_iff_isUnit_det _).2 (hdet z hz)) i i
    exact (continuous_norm.continuousAt.comp hi.continuousAt).continuousWithinAt
  have hInvBound (i : Fin n) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖(g z)⁻¹ i i‖ ≤ C := by
    let f := fun z => ‖(g z)⁻¹ i i‖
    exact hCompactUpperBound f (hInvCont i)
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let C : ι → ℝ := fun t => Classical.choose
    (hCurvBound t.1 t.2.1 t.2.2.1 t.2.2.2)
  have hCnonneg (t : ι) : 0 ≤ C t :=
    (Classical.choose_spec (hCurvBound t.1 t.2.1 t.2.2.1 t.2.2.2)).1
  have hCbound (t : ι) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      ‖chartCurvature g z t.1 t.2.1 t.2.2.1 t.2.2.2‖ ≤ C t :=
    (Classical.choose_spec (hCurvBound t.1 t.2.1 t.2.2.1 t.2.2.2)).2 z hz
  let D : Fin n → ℝ := fun i => Classical.choose (hInvBound i)
  have hDnonneg (i : Fin n) : 0 ≤ D i := (Classical.choose_spec (hInvBound i)).1
  have hDbound (i : Fin n) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      ‖(g z)⁻¹ i i‖ ≤ D i := (Classical.choose_spec (hInvBound i)).2 z hz
  let H : ℝ := ∑ i, D i + 1
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (Finset.sum_nonneg fun i hi => hDnonneg i) (by norm_num)
  have hEntry (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K)
      (P : Matrix (Fin n) (Fin n) ℂ)
      (hP : P.transpose * g z * P.map star = 1) (i j : Fin n) : ‖P i j‖ ≤ H := by
    have h := fixedChart_frame_entry_bound (g z) P hP i j
    have hD : ‖(g z)⁻¹ i i‖ ≤ ∑ t, D t :=
      (hDbound i z hz).trans (Finset.single_le_sum
        (fun t ht => hDnonneg t) (Finset.mem_univ i))
    exact h.trans (by dsimp [H]; linarith)
  let B : ℝ := ∑ a, ∑ b, ∑ c, ∑ d,
    H * H * H * H * C ⟨a, ⟨b, ⟨c, d⟩⟩⟩
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb =>
      Finset.sum_nonneg fun c hc => Finset.sum_nonneg fun d hd => by
        have hC := hCnonneg (⟨a, ⟨b, ⟨c, d⟩⟩⟩ : ι)
        positivity
  · intro z hz P hP p q j k
    calc
      ‖∑ a, ∑ b, ∑ c, ∑ d,
          P a p * star (P b q) * P c j * star (P d k) * chartCurvature g z a b c d‖
        ≤ ∑ a, ∑ b, ∑ c, ∑ d,
          ‖P a p * star (P b q) * P c j * star (P d k) * chartCurvature g z a b c d‖ := by
          calc
            ‖∑ a, ∑ b, ∑ c, ∑ d, _‖ ≤ ∑ a, ‖∑ b, ∑ c, ∑ d, _‖ :=
              norm_sum_le Finset.univ (fun a : Fin n => ∑ b, ∑ c, ∑ d, _)
            _ ≤ ∑ a, ∑ b, ‖∑ c, ∑ d, _‖ := by
              apply Finset.sum_le_sum
              intro a ha
              exact norm_sum_le Finset.univ (fun b : Fin n => ∑ c, ∑ d, _)
            _ ≤ ∑ a, ∑ b, ∑ c, ‖∑ d, _‖ := by
              apply Finset.sum_le_sum
              intro a ha
              apply Finset.sum_le_sum
              intro b hb
              exact norm_sum_le Finset.univ (fun c : Fin n => ∑ d, _)
            _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, ‖_‖ := by
              apply Finset.sum_le_sum
              intro a ha
              apply Finset.sum_le_sum
              intro b hb
              apply Finset.sum_le_sum
              intro c hc
              exact norm_sum_le Finset.univ (fun d : Fin n => _)
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          ‖P a p‖ * ‖P b q‖ * ‖P c j‖ * ‖P d k‖ * ‖chartCurvature g z a b c d‖ := by
          simp_rw [norm_mul, norm_star]
      _ ≤ B := by
        dsimp [B]
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        apply Finset.sum_le_sum
        intro c hc
        apply Finset.sum_le_sum
        intro d hd
        have hPa := hEntry z hz P hP a p
        have hPb := hEntry z hz P hP b q
        have hPc := hEntry z hz P hP c j
        have hPd := hEntry z hz P hP d k
        have hR := hCbound ⟨a, ⟨b, ⟨c, d⟩⟩⟩ z hz
        have hR0 := hCnonneg (⟨a, ⟨b, ⟨c, d⟩⟩⟩ : ι)
        have hnorma : 0 ≤ ‖P a p‖ := norm_nonneg _
        have hnormb : 0 ≤ ‖P b q‖ := norm_nonneg _
        have hnormc : 0 ≤ ‖P c j‖ := norm_nonneg _
        have hnormd : 0 ≤ ‖P d k‖ := norm_nonneg _
        gcongr

private theorem fixedChart_local_frame_curvature_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (Q : Matrix (Fin n) (Fin n) ℂ),
        Q.transpose * ω₀.metricInChart x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) * Q.map star = 1 →
          ∀ p q j k : Fin n,
            ‖∑ a, ∑ b, ∑ c, ∑ d,
                Q a p * star (Q b q) * Q c j * star (Q d k) *
                  chartCurvature (fun z => ω₀.metricInChart x z)
                    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b c d‖ ≤ C := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z₀ := c x
  obtain ⟨r, hr, hrTarget⟩ := fixedChartClosedBall_subset_target (n := n) x
  let K := Metric.closedBall z₀ r
  have hK : IsCompact K := isCompact_closedBall z₀ r
  have hKt : K ⊆ c.target := hrTarget
  obtain ⟨C, hC0, hC⟩ := fixedChart_compact_contraction_bound ω₀ x K hK hKt
  let U : Set M := c.source ∩ c ⁻¹' Metric.ball z₀ r
  refine ⟨U, ?_, ?_, ?_, C, hC0, ?_⟩
  · exact isOpen_extChartAt_preimage' x Metric.isOpen_ball
  · refine ⟨mem_extChartAt_source x, ?_⟩
    change c x ∈ Metric.ball z₀ r
    exact Metric.mem_ball_self hr
  · exact Set.inter_subset_left
  · intro y hy Q hQ p q j k
    have hy' : c y ∈ Metric.ball z₀ r := hy.2
    have hyK : c y ∈ K := Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy'))
    simpa [K, c, z₀] using hC (c y) hyK Q hQ p q j k

/-- Local uniform bound on the fourfold fixed-chart curvature contraction, for every frame
unitary with respect to the metric in that same fixed chart. -/
theorem exists_local_fixed_chart_frame_curvature_bound (ω₀ : KahlerForm n M) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (Q : Matrix (Fin n) (Fin n) ℂ),
        Q.transpose * ω₀.metricInChart x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) * Q.map star = 1 →
          ∀ p q j k : Fin n,
            ‖∑ a, ∑ b, ∑ c, ∑ d,
                Q a p * star (Q b q) * Q c j * star (Q d k) *
                  chartCurvature (fun z ↦ ω₀.metricInChart x z)
                    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b c d‖ ≤ C := by
  exact fixedChart_local_frame_curvature_bound ω₀ x

end KahlerForm
