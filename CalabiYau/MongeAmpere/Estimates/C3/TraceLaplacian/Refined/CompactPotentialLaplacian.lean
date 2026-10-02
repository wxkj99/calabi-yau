module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.MixedPotentialDerivative
public import CalabiYau.Geometry.Kahler.Laplacian

/-!
# Reference Laplacian on one compact chart piece

The fixed smooth reference metric has bounded inverse coefficients on a fixed
compact subset of a chart. The chart formula for its complex Laplacian contracts
these coefficients against the mixed Wirtinger Hessian of a real potential.
This is deliberately a fixed-chart statement; the selected chart at a varying
point has no uniformly controlled scale. Source: Székelyhidi, *An Introduction
to Extremal Kähler Metrics*, §3.3, Lemma 3.10, pp. 45–46.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal ComplexOrder Topology
open ContinuousAlternatingMap Filter

namespace KahlerForm

/- These Euclidean Wirtinger definitions and their bridge are private copies of
   the already-proved local calculation in Kahler/Laplacian/Cofactor. That
   module is a non-public import of Laplacian, so the child keeps its frozen
   import boundary. -/
private noncomputable def chartPartialBar {n : ℕ}
    (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  ((fderiv ℝ u z (EuclideanSpace.single j 1) : ℂ) +
    Complex.I * fderiv ℝ u z (Complex.I • EuclideanSpace.single j 1)) / 2

private noncomputable def chartPartialZComplex {n : ℕ}
    (u : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ u z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ u z (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem chartPartialZComplex_chartPartialBar {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (j k : Fin n) :
    chartPartialZComplex (fun w ↦ chartPartialBar f w k) z j =
      complexHessian f z j k := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ f w e) z d = fderiv ℝ (fderiv ℝ f) z d e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const e)]
    simp
  have hsecondComplex (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ f w e : ℂ)) z d =
        (fderiv ℝ (fderiv ℝ f) z d e : ℂ) := by
    have hreal := hfd.clm_apply (differentiableAt_const e)
    have h := (Complex.ofRealCLM.hasFDerivAt.comp z hreal.hasFDerivAt).fderiv
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    change fderiv ℝ (Complex.ofRealCLM ∘ (fun w ↦ fderiv ℝ f w e)) z d = _
    simpa [hsecond] using h'
  have hbarDeriv (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ chartPartialBar f w k) z d =
        ((fderiv ℝ (fderiv ℝ f) z d (EuclideanSpace.single k 1) : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ f) z d
            (Complex.I • EuclideanSpace.single k 1)) / 2 := by
    let A := fun w ↦ (fderiv ℝ f w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w ↦ (fderiv ℝ f w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hA : DifferentiableAt ℝ A z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hB : DifferentiableAt ℝ B z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hnum : DifferentiableAt ℝ (fun w ↦ A w + Complex.I * B w) z :=
      hA.add (hB.const_mul Complex.I)
    have hfun : (fun w ↦ chartPartialBar f w k) =
        fun w ↦ (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun, fderiv_const_mul hnum (2 : ℂ)⁻¹, fderiv_fun_add hA (hB.const_mul Complex.I),
      fderiv_const_mul hB Complex.I]
    dsimp [A, B]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsecondComplex d (EuclideanSpace.single k 1),
      hsecondComplex d (Complex.I • EuclideanSpace.single k 1)]
    ring
  change ((fderiv ℝ (fun w ↦ chartPartialBar f w k) z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ (fun w ↦ chartPartialBar f w k) z
      (Complex.I • EuclideanSpace.single j 1)) / 2) = _
  rw [hbarDeriv (EuclideanSpace.single j 1),
    hbarDeriv (Complex.I • EuclideanSpace.single j 1),
    complexHessian_apply hf j k]
  ring_nf
  simp [Complex.I_sq]
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem exists_uniform_chart_inverse_entry_bound
    (ω₀ : KahlerForm n M) (x₀ : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ i j : Fin n,
      ‖(ω₀.metricInChart x₀ z)⁻¹ i j‖ ≤ B := by
  classical
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target
  let g := fun z ↦ ω₀.metricInChart x₀ z
  have hU : IsOpen U := isOpen_extChartAt_target x₀
  have hgCont : ContinuousOn g U := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (ω₀.contDiffOn_metricInChart x₀ i j).continuousOn
  have hinv (i j : Fin n) : ContinuousOn (fun z ↦ (g z)⁻¹ i j) U := by
    intro z hz
    have hG : ContinuousAt g z := (hgCont z hz).continuousAt (hU.mem_nhds hz)
    have hunit : IsUnit (g z).det :=
      (Matrix.isUnit_iff_isUnit_det (g z)).mp (ω₀.posDef_metricInChart x₀ hz).isUnit
    have hdet : (g z).det ≠ 0 := hunit.ne_zero
    have hdetAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) (g z) := by fun_prop
    have hAdjAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.adjugate) (g z) := by fun_prop
    have hinvDetAt : ContinuousAt
        (fun A : Matrix (Fin n) (Fin n) ℂ ↦ Ring.inverse A.det) (g z) := by
      have hscalar : ContinuousAt (fun w : ℂ ↦ Ring.inverse w) (g z).det := by
        simpa only [Ring.inverse_eq_inv] using continuousAt_inv₀ hdet
      exact hscalar.comp hdetAt
    have hinvMatrix : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A⁻¹) (g z) := by
      change ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ ↦
        Ring.inverse A.det • A.adjugate) (g z)
      exact hinvDetAt.smul hAdjAt
    have hinvMatrixAt : ContinuousAt (fun w ↦ (g w)⁻¹) z := hinvMatrix.comp hG
    have hinvEntry : ContinuousAt (fun w ↦ (g w)⁻¹ i j) z := by
      have h₁ := continuousAt_pi.mp hinvMatrixAt i
      exact continuousAt_pi.mp h₁ j
    exact hinvEntry.continuousWithinAt
  have hinvNorm (i j : Fin n) : ContinuousOn (fun z ↦ ‖(g z)⁻¹ i j‖) U :=
    (hinv i j).norm
  choose B hB0 hB using fun i j ↦
    (hK.bddAbove_image ((hinvNorm i j).mono hKt)).exists_ge 0
  refine ⟨∑ i, ∑ j, B i j, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i hi ↦ Finset.sum_nonneg (fun j hj ↦ hB0 i j))
  · intro z hz i j
    have hval : ‖(g z)⁻¹ i j‖ ≤ B i j := hB i j _ (Set.mem_image_of_mem _ hz)
    calc
      ‖(g z)⁻¹ i j‖ ≤ B i j := hval
      _ ≤ ∑ a, ∑ b, B a b := by
        apply le_trans (Finset.single_le_sum (fun b hb ↦ hB0 i b) (Finset.mem_univ j))
        exact Finset.single_le_sum
          (fun a ha ↦ Finset.sum_nonneg (fun b hb ↦ hB0 a b)) (Finset.mem_univ i)

variable [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- A bound for the correctly normalized mixed derivatives on one compact chart
piece bounds the *intrinsic* reference Laplacian at points represented by that
piece. The metric is fixed; the constant may depend on the chart and compact
piece but not on the family member. In dimension zero both sides vanish. -/
theorem exists_uniform_c3RefinedTrace_compactChartPotentialLaplacian_bound
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1)
    (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target)
    (hMixed : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ z ∈ K, ∀ i j : Fin n,
      ‖wirtingerDerivInChart
        (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ ((p.1 ∘ (extChartAt
            𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) v : ℂ)) w j) z i‖ ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ S, ∀ z ∈ K,
      |ω₀.laplacian p.1 ((extChartAt
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z)| ≤ A := by
  obtain ⟨C, hC0, hC⟩ := hMixed
  obtain ⟨B, hB0, hB⟩ := exists_uniform_chart_inverse_entry_bound ω₀ x₀ K hK hKt
  refine ⟨(n : ℝ) ^ 2 * B * C, by positivity, ?_⟩
  intro p hp z hz
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let F : EuclideanSpace ℂ (Fin n) → ℝ := p.1 ∘ ψ.symm
  have hU : IsOpen ψ.target := isOpen_extChartAt_target x₀
  have hFOn : ContDiffOn ℝ ∞ F ψ.target := by
    have hpMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 Set.univ :=
      contMDiffOn_univ.mpr (hS p hp)
    exact (hpMD.comp (contMDiffOn_extChartAt_symm x₀)
      (by intro w hw; simp)).contDiffOn
  have hFAt : ContDiffAt ℝ ∞ F z := hFOn.contDiffAt (hU.mem_nhds (hKt hz))
  have hF₂ : ContDiffAt ℝ 2 F z := hFAt.of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hH (i j : Fin n) : ‖complexHessian F z i j‖ ≤ C := by
    have hbarEq : (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ ((F v : ℝ) : ℂ)) w j) =ᶠ[𝓝 z]
        (fun w ↦ chartPartialBar F w j) := by
      filter_upwards [hU.mem_nhds (hKt hz)] with w hw
      have hFw : ContDiffAt ℝ ∞ F w := hFOn.contDiffAt (hU.mem_nhds hw)
      have hcast : fderiv ℝ (fun v ↦ ((F v : ℝ) : ℂ)) w =
          Complex.ofRealCLM.comp (fderiv ℝ F w) := by
        change fderiv ℝ (Complex.ofRealCLM ∘ F) w = _
        exact (Complex.ofRealCLM.hasFDerivAt.comp w (hFw.differentiableAt (by norm_num)).hasFDerivAt).fderiv
      have hbar := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦
        (L (EuclideanSpace.single j 1) + Complex.I * L (Complex.I • EuclideanSpace.single j 1)) / 2)
        hcast
      simpa [c3RefinedTracePartialBar, chartPartialBar, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply] using hbar
    have hbarDeriv := hbarEq.fderiv_eq (𝕜 := ℝ)
    have hmixedEq : wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ ((F v : ℝ) : ℂ)) w j) z i =
        chartPartialZComplex (fun w ↦ chartPartialBar F w j) z i := by
      change chartPartialZComplex (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ ((F v : ℝ) : ℂ)) w j) z i = _
      simp only [chartPartialZComplex]
      rw [hbarDeriv]
    have hbridge := chartPartialZComplex_chartPartialBar F z hF₂ i j
    have hbound := hC p hp z hz i j
    calc
      ‖complexHessian F z i j‖ =
          ‖chartPartialZComplex (fun w ↦ chartPartialBar F w j) z i‖ := by rw [← hbridge]
      _ = ‖wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ ((F v : ℝ) : ℂ)) w j) z i‖ := by rw [← hmixedEq]
      _ ≤ C := hbound
  have hy : ψ.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
    simpa [ψ, ← extChartAt_source] using ψ.map_target (hKt hz)
  have hLap := ω₀.laplacian_eq_inChart (hS p hp) x₀ (y := ψ.symm z) hy
  rw [ψ.right_inv (hKt hz)] at hLap
  have htrace : |Complex.re ((ω₀.metricInChart x₀ z)⁻¹ * complexHessian F z).trace| ≤
      (n : ℝ) ^ 2 * B * C := by
    calc
      |Complex.re ((ω₀.metricInChart x₀ z)⁻¹ * complexHessian F z).trace| ≤
          ‖((ω₀.metricInChart x₀ z)⁻¹ * complexHessian F z).trace‖ :=
        Complex.abs_re_le_norm _
      _ = ‖∑ i : Fin n, ∑ j : Fin n,
          (ω₀.metricInChart x₀ z)⁻¹ i j * complexHessian F z j i‖ := by
        simp [Matrix.mul_apply, Matrix.trace]
      _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          ‖(ω₀.metricInChart x₀ z)⁻¹ i j * complexHessian F z j i‖ := by
        calc
          _ ≤ ∑ i : Fin n, ‖∑ j : Fin n,
              (ω₀.metricInChart x₀ z)⁻¹ i j * complexHessian F z j i‖ := norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            exact norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, B * C := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        calc
          ‖(ω₀.metricInChart x₀ z)⁻¹ i j * complexHessian F z j i‖ ≤
              ‖(ω₀.metricInChart x₀ z)⁻¹ i j‖ * ‖complexHessian F z j i‖ := norm_mul_le _ _
          _ ≤ B * C := mul_le_mul (hB z hz i j) (hH j i)
            (norm_nonneg _) hB0
      _ = (n : ℝ) ^ 2 * B * C := by simp [Finset.sum_const, Fintype.card_fin, mul_assoc]; ring
  rw [hLap]
  exact htrace

end KahlerForm
