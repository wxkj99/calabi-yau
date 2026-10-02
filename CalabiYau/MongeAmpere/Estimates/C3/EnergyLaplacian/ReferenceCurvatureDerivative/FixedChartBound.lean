module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
public import CalabiYau.Geometry.Kahler.Curvature.Chart

/-!
# Fixed-chart compact bound for the reference curvature derivative

The coefficient and inverse-diagonal estimates are taken in one fixed chart.
Normalized column entries are bounded by a chart-dependent constant, not by
one. Compact coordinate neighborhoods then give the local manifold bound.
Source: Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45.
-/

public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

open scoped NNReal Matrix.Norms.Elementwise MatrixOrder ComplexOrder

private theorem auxiliary_chartPartialZComplex_contDiffAt
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    ContDiffAt ℝ ∞ (fun w => chartPartialZComplex F w p) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialZComplex
  fun_prop (disch := assumption)

private theorem auxiliary_det_contDiffAt
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

private theorem auxiliary_adjugate_entry_contDiffAt
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
      · simp only [Matrix.updateRow_apply, if_neg ha]
        exact hentry a b
    have hmatrix : ContDiffAt ℝ ∞
        (fun w => (A w).updateRow j (Pi.single i 1)) z := by
      apply contDiffAt_pi.mpr
      intro a
      apply contDiffAt_pi.mpr
      intro b
      exact hupdate a b
    exact auxiliary_det_contDiffAt _ z hmatrix
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w hw
  exact Matrix.adjugate_apply (A w) i j

private theorem auxiliary_matrix_inverse_entry_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) (hunit : IsUnit (A z).det) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (A w)⁻¹ i j) z := by
  have hdet := auxiliary_det_contDiffAt A z hA
  have hinvdet : ContDiffAt ℝ ∞ (fun w => ((A w).det)⁻¹) z := by
    have hnz : (A z).det ≠ 0 := hunit.ne_zero
    exact (contDiffAt_inv ℝ hnz).comp z hdet
  have hadj := auxiliary_adjugate_entry_contDiffAt A z hA i j
  have hentry : ContDiffAt ℝ ∞
      (fun w => ((A w).det)⁻¹ * (A w).adjugate i j) z := hinvdet.mul hadj
  apply hentry.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w
  rw [Matrix.inv_def]
  simp [Matrix.smul_apply]

private theorem auxiliary_chartPartialBarComplex_contDiffAt
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (q : Fin n) :
    ContDiffAt ℝ ∞ (fun w => chartPartialBarComplex F w q) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialBarComplex
  fun_prop (disch := assumption)

private theorem auxiliary_fixed_chart_compact_inverse_diagonal_bound
    (ω₀ : KahlerForm n M) (x : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ K, ∀ i : Fin n,
      ‖(ω₀.metricInChart x z)⁻¹ i i‖ ≤ Q := by
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
    have hinv : ContDiffAt ℝ ∞ (fun w => (g w)⁻¹) z :=
      by
        apply contDiffAt_pi.mpr
        intro a
        apply contDiffAt_pi.mpr
        intro b
        exact auxiliary_matrix_inverse_entry_contDiffAt g z hg hdet a b
    exact (continuous_norm.continuousAt.comp
      (contDiffAt_pi.mp (contDiffAt_pi.mp hinv i) i).continuousAt).continuousWithinAt
  have hBound (i : Fin n) :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ K, ‖(g z)⁻¹ i i‖ ≤ D := by
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
  · intro z hz i
    have hsingle : D i ≤ ∑ j, D j :=
      Finset.single_le_sum (fun j hj => hDnonneg j) (Finset.mem_univ i)
    exact (hDbound i z hz).trans (by dsimp [Q]; linarith)

private theorem auxiliary_frame_entry_bound_of_chart_inverse_diagonal
    {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℂ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hP : P.transpose * A * P.map star = 1)
    (hdiag : ∀ i, RCLike.re (A⁻¹ i i) ≤ Q) :
    ∀ i j, ‖P i j‖ ≤ Real.sqrt Q := by
  have h' : (P.transpose * A) * P.map star = 1 := by
    simpa [Matrix.mul_assoc] using hP
  have hleft : P.map star * (P.transpose * A) = 1 := mul_eq_one_comm.1 h'
  have hleft' : (P.map star * P.transpose) * A = 1 := by
    simpa [Matrix.mul_assoc] using hleft
  have hAinv : A⁻¹ = P.map star * P.transpose := Matrix.inv_eq_left_inv hleft'
  intro i j
  have hsum : ∑ a : Fin n, Complex.normSq (P i a) = (A⁻¹ i i).re := by
    have hmat := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X i i) hAinv
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply] at hmat
    have hre := congrArg Complex.re hmat
    rw [Complex.re_sum] at hre
    have hterm (z : ℂ) : (star z * z).re = Complex.normSq z := by
      have hh := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))
      simpa using hh.symm
    simp_rw [hterm] at hre
    exact hre.symm
  have hsumEntry : Complex.normSq (P i j) ≤ ∑ a : Fin n, Complex.normSq (P i a) :=
    Finset.single_le_sum (fun a ha => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have hdiagBound : (A⁻¹ i i).re ≤ Q := hdiag i
  have hsq : ‖P i j‖ ^ 2 ≤ Q := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hsumEntry.trans (hsum ▸ hdiagBound)
  have hnonneg : 0 ≤ ‖P i j‖ := norm_nonneg _
  have hsqrt : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt hQ]

private theorem auxiliary_fixed_chart_compact_frame_entry_bound
    (ω₀ : KahlerForm n M) (x : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ K, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
      P.transpose * ω₀.metricInChart x z * P.map star = 1 →
        ∀ i j, ‖P i j‖ ≤ Real.sqrt Q := by
  obtain ⟨Q, hQ, hInvDiag⟩ :=
    auxiliary_fixed_chart_compact_inverse_diagonal_bound ω₀ x K hK hKt
  refine ⟨Q, hQ, ?_⟩
  intro z hz P hP i j
  apply auxiliary_frame_entry_bound_of_chart_inverse_diagonal
    (ω₀.metricInChart x z) P Q hQ hP ?_ i j
  intro a
  exact (le_abs_self _).trans
    ((Complex.abs_re_le_norm _).trans (hInvDiag z hz a))

private noncomputable def auxiliaryReferenceCurvatureCovariantDerivativeInChart
    (ω₀ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (s p q j k : Fin n) : ℂ :=
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  wirtingerDerivInChart (fun w ↦ chartCurvature g₀ w p q j k) z s -
    ∑ a : Fin n, christoffelInChart g₀ z a s p * chartCurvature g₀ z a q j k -
    ∑ a : Fin n, christoffelInChart g₀ z a s j * chartCurvature g₀ z p q a k

private theorem auxiliary_reference_curvature_covariant_derivative_contDiffAt
    (ω₀ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (s p q j k : Fin n) :
    ContDiffAt ℝ ∞
      (fun w => auxiliaryReferenceCurvatureCovariantDerivativeInChart ω₀ x w s p q j k) z := by
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => ω₀.metricInChart x w
  have hgEntry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z := by
    exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hg : ContDiffAt ℝ ∞ g z := by
    apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact hgEntry a b
  have hdet : IsUnit (g z).det :=
    (Matrix.isUnit_iff_isUnit_det (g z)).mp (ω₀.posDef_metricInChart x hz).isUnit
  have hinv : ContDiffAt ℝ ∞ (fun w => (g w)⁻¹) z :=
    by
      apply contDiffAt_pi.mpr
      intro a
      apply contDiffAt_pi.mpr
      intro b
      exact auxiliary_matrix_inverse_entry_contDiffAt g z hg hdet a b
  have hinvEntry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => (g w)⁻¹ a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hinv a) b
  have hZ (a b r : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartPartialZComplex (fun v => g v a b) w r) z :=
    auxiliary_chartPartialZComplex_contDiffAt _ z (hgEntry a b) r
  have hBar (a b r : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartPartialBarComplex (fun v => g v a b) w r) z :=
    auxiliary_chartPartialBarComplex_contDiffAt _ z (hgEntry a b) r
  have hZBar (a b r t : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartPartialZComplex
        (fun v => chartPartialBarComplex (fun u => g u a b) v t) w r) z :=
    auxiliary_chartPartialZComplex_contDiffAt _ z (hBar a b t) r
  have hCurv (a b c d : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartCurvature g w a b c d) z := by
    have hterm (i j : Fin n) : ContDiffAt ℝ ∞
        (fun w => (g w)⁻¹ j i *
          chartPartialZComplex (fun v => g v c j) w a *
          chartPartialBarComplex (fun v => g v i d) w b) z := by
      exact (hinvEntry j i).mul (hZ c j a) |>.mul (hBar i d b)
    have hsum (i : Fin n) : ContDiffAt ℝ ∞
        (fun w => ∑ j : Fin n,
          (g w)⁻¹ j i * chartPartialZComplex (fun v => g v c j) w a *
            chartPartialBarComplex (fun v => g v i d) w b) z := by
      apply ContDiffAt.sum
      intro j hj
      exact hterm i j
    have hdouble : ContDiffAt ℝ ∞
        (fun w => ∑ i : Fin n, ∑ j : Fin n,
          (g w)⁻¹ j i * chartPartialZComplex (fun v => g v c j) w a *
            chartPartialBarComplex (fun v => g v i d) w b) z := by
      apply ContDiffAt.sum
      intro i hi
      exact hsum i
    change ContDiffAt ℝ ∞
      (fun w => -chartPartialZComplex
        (fun v => chartPartialBarComplex (fun u => g u c d) v b) w a +
        ∑ i : Fin n, ∑ j : Fin n,
          (g w)⁻¹ j i * chartPartialZComplex (fun v => g v c j) w a *
            chartPartialBarComplex (fun v => g v i d) w b) z
    exact (hZBar c d a b).neg.add hdouble
  have hChrist (a b c : Fin n) : ContDiffAt ℝ ∞
      (fun w => christoffelInChart g w a b c) z := by
    unfold christoffelInChart
    apply ContDiffAt.sum
    intro l hl
    have hpartial : ContDiffAt ℝ ∞
        (fun w => wirtingerDerivInChart (fun v => g v c l) w b) z := by
      change ContDiffAt ℝ ∞ (fun w => chartPartialZComplex (fun v => g v c l) w b) z
      exact hZ c l b
    exact (hinvEntry l a).mul hpartial
  have hcurvPartial : ContDiffAt ℝ ∞
      (fun w => wirtingerDerivInChart (fun v => chartCurvature g v p q j k) w s) z := by
    change ContDiffAt ℝ ∞ (fun w => chartPartialZComplex
      (fun v => chartCurvature g v p q j k) w s) z
    exact auxiliary_chartPartialZComplex_contDiffAt _ z (hCurv p q j k) s
  change ContDiffAt ℝ ∞ (fun w =>
    wirtingerDerivInChart (fun v => chartCurvature g v p q j k) w s -
      ∑ a : Fin n, christoffelInChart g w a s p * chartCurvature g w a q j k -
      ∑ a : Fin n, christoffelInChart g w a s j * chartCurvature g w p q a k) z
  fun_prop (disch := assumption)

private theorem auxiliary_fixed_chart_compact_covariant_derivative_component_bound
    (ω₀ : KahlerForm n M) (x : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ s p q j k : Fin n,
      ‖auxiliaryReferenceCurvatureCovariantDerivativeInChart ω₀ x z s p q j k‖ ≤ B := by
  classical
  let ι := Fin n × (Fin n × (Fin n × (Fin n × Fin n)))
  have hcomponentBound (t : ι) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
        ‖auxiliaryReferenceCurvatureCovariantDerivativeInChart ω₀ x z
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2‖ ≤ C := by
    let f : EuclideanSpace ℂ (Fin n) → ℝ := fun z =>
      ‖auxiliaryReferenceCurvatureCovariantDerivativeInChart ω₀ x z
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2‖
    have hf : ContinuousOn f K := by
      intro z hz
      exact (auxiliary_reference_curvature_covariant_derivative_contDiffAt ω₀ x z
        (hKt hz) t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).continuousAt.norm.continuousWithinAt
    have hbdd : BddAbove (f '' K) := hK.bddAbove_image hf
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro z hz
    exact (hC (Set.mem_image_of_mem f hz)).trans (le_max_right _ _)
  let C : ι → ℝ := fun t => Classical.choose (hcomponentBound t)
  have hCnonneg (t : ι) : 0 ≤ C t := (Classical.choose_spec (hcomponentBound t)).1
  have hCbound (t : ι) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      ‖auxiliaryReferenceCurvatureCovariantDerivativeInChart ω₀ x z
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2‖ ≤ C t :=
    (Classical.choose_spec (hcomponentBound t)).2 z hz
  let B : ℝ := ∑ t, C t
  refine ⟨B, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun t ht => hCnonneg t)
  · intro z hz s p q j k
    let t : ι := ⟨s, ⟨p, ⟨q, ⟨j, k⟩⟩⟩⟩
    have hsingle : C t ≤ ∑ t, C t :=
      Finset.single_le_sum (fun t ht => hCnonneg t) (Finset.mem_univ t)
    exact (hCbound t z hz).trans (by simpa [B] using hsingle)

private theorem norm_fin_fivefold_sum_le {n : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → E) :
    ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e‖ ≤
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ‖f a b c d e‖ := by
  calc
    ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e‖ ≤
        ∑ a, ‖∑ b, ∑ c, ∑ d, ∑ e, f a b c d e‖ := norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ‖∑ c, ∑ d, ∑ e, f a b c d e‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ∑ c, ‖∑ d, ∑ e, f a b c d e‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, ‖∑ e, f a b c d e‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      exact norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ‖f a b c d e‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sum_le _ _

/-- Compact fixed-chart bound, uniform over every reference-normalized frame.
Target containment states the domain of smoothness and positive definiteness. -/
theorem exists_compact_fixed_chart_c3_curvature_derivative_bound
    (ω₀ : KahlerForm n M) (x : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
      P.transpose * ω₀.metricInChart x z * P.map star = 1 →
        ∀ s p q j k : Fin n,
          ‖c3FiveSlotFrameContraction P
            (c3CovariantFourTensorZJet (christoffelInChart (ω₀.metricInChart x) z)
              (chartCurvature (ω₀.metricInChart x) z)
              (fun a b c d e => chartPartialZComplex
                (fun w => chartCurvature (ω₀.metricInChart x) w b c d e) z a))
            s p q j k‖ ≤ B := by
  classical
  obtain ⟨Q, hQ, hFrame⟩ :=
    auxiliary_fixed_chart_compact_frame_entry_bound ω₀ x K hK hKt
  obtain ⟨C, hC, hComponent⟩ :=
    auxiliary_fixed_chart_compact_covariant_derivative_component_bound ω₀ x K hK hKt
  let L : ℝ := Real.sqrt Q
  let D : ℝ := L * L * L * L * L * C
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hD : 0 ≤ D := by positivity
  let B : ℝ := ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n, D
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro d hd
    exact Finset.sum_nonneg fun e he => hD
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => ω₀.metricInChart x w
  have hTensor (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K)
      (s p q j k : Fin n) :
      ‖c3CovariantFourTensorZJet (christoffelInChart g z)
        (chartCurvature g z)
        (fun a b c d e => chartPartialZComplex
          (fun w => chartCurvature g w b c d e) z a) s p q j k‖ ≤ C := by
    change ‖auxiliaryReferenceCurvatureCovariantDerivativeInChart
      ω₀ x z s p q j k‖ ≤ C
    exact hComponent z hz s p q j k
  have hTerm (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K)
      (P : Matrix (Fin n) (Fin n) ℂ)
      (hP : P.transpose * g z * P.map star = 1)
      (s p q j k a b c d e : Fin n) :
      ‖P a s * P b p * star (P c q) * P d j * star (P e k) *
        c3CovariantFourTensorZJet (christoffelInChart g z)
          (chartCurvature g z)
          (fun u v w r t => chartPartialZComplex
            (fun y => chartCurvature g y v w r t) z u) a b c d e‖ ≤ D := by
    have h1 := hFrame z hz P hP a s
    have h2 := hFrame z hz P hP b p
    have h3 := hFrame z hz P hP c q
    have h4 := hFrame z hz P hP d j
    have h5 := hFrame z hz P hP e k
    have h6 := hTensor z hz a b c d e
    simp only [norm_mul, norm_star]
    dsimp [D, L]
    gcongr
  refine ⟨B, hB, ?_⟩
  intro z hz P hP s p q j k
  let F : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ := fun a b c d e =>
    P a s * P b p * star (P c q) * P d j * star (P e k) *
      c3CovariantFourTensorZJet (christoffelInChart g z)
        (chartCurvature g z)
        (fun u v w r t => chartPartialZComplex
          (fun y => chartCurvature g y v w r t) z u) a b c d e
  have hFbound (a b c d e : Fin n) : ‖F a b c d e‖ ≤ D := by
    dsimp [F]
    exact hTerm z hz P (by simpa [g] using hP) s p q j k a b c d e
  have hRaw :
      ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e‖ ≤ B := by
    calc
      ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e‖ ≤
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ‖F a b c d e‖ := norm_fin_fivefold_sum_le F
      _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, D := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          apply Finset.sum_le_sum
          intro c hc
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro e he
          exact hFbound a b c d e
      _ = B := rfl
  have hNormSum :
      ‖c3FiveSlotFrameContraction P
        (c3CovariantFourTensorZJet (christoffelInChart g z)
          (chartCurvature g z)
          (fun a b c d e => chartPartialZComplex
            (fun w => chartCurvature g w b c d e) z a)) s p q j k‖ ≤ B := by
    change ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      P a s * P b p * star (P c q) * P d j * star (P e k) *
        c3CovariantFourTensorZJet (christoffelInChart g z)
          (chartCurvature g z)
          (fun u v w r t => chartPartialZComplex
            (fun y => chartCurvature g y v w r t) z u) a b c d e‖ ≤ B
    simpa only [F] using hRaw
  exact hNormSum

/-- Pass the compact fixed-chart bound to a source-contained open neighborhood.
No continuity of the chart chosen at a varying point is used. -/
theorem exists_local_fixed_chart_c3_curvature_derivative_bound
    (ω₀ : KahlerForm n M) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ U, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
        P.transpose * ω₀.metricInChart x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) * P.map star = 1 →
          ∀ s p q j k : Fin n,
            ‖c3FiveSlotFrameContraction P
              (c3CovariantFourTensorZJet
                (christoffelInChart (ω₀.metricInChart x)
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
                (chartCurvature (ω₀.metricInChart x)
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
                (fun a b c d e => chartPartialZComplex
                  (fun w => chartCurvature (ω₀.metricInChart x) w b c d e)
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a))
              s p q j k‖ ≤ B := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  obtain ⟨K, hK, hxK, hKt⟩ := exists_compact_subset (isOpen_extChartAt_target x)
    (c.map_source (mem_extChartAt_source x))
  obtain ⟨B, hB, hbound⟩ :=
    exists_compact_fixed_chart_c3_curvature_derivative_bound ω₀ x K hK hKt
  let U : Set M := c.source ∩ c ⁻¹' interior K
  refine ⟨U, isOpen_extChartAt_preimage' x isOpen_interior,
    ⟨mem_extChartAt_source x, hxK⟩, Set.inter_subset_left, B, hB, ?_⟩
  intro y hy P hP s p q j k
  exact hbound (c y) (interior_subset hy.2) P hP s p q j k

end KahlerForm
