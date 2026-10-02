module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientIdentity
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.CompactSecant
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.HolderAlgebra
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.HolderProducts

/-!
# Uniform Hölder control of the corrected difference-quotient forcing

The input is entrywise control of the actual averaged inverse. Smooth prescribed data and smooth
background coefficients supply their own secant radii. Their common positive minimum also ensures
translated endpoint containment. The conclusion uses the actual minus real trace correction.
-/

public section

open scoped Manifold ContDiff NNReal Topology Matrix.Norms.Elementwise
open Set

namespace KahlerForm

private theorem exists_compact_translated_chart_neighborhood
    {n : ℕ} (K target : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKtarget : K ⊆ target) (htarget : IsOpen target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K' : Set (EuclideanSpace ℂ (Fin n)),
      IsCompact K' ∧ K' ⊆ target ∧ K ⊆ K' ∧
      ∀ h : ℝ, |h| < δ → ∀ z ∈ K, z + h • v ∈ K' := by
  let E := EuclideanSpace ℂ (Fin n)
  let N : Set (E × E) := {p | p.1 + p.2 ∈ target}
  have hNopen : IsOpen N := by
    have hadd : Continuous fun p : E × E ↦ p.1 + p.2 := by fun_prop
    exact htarget.preimage hadd
  have hN : K ×ˢ ({0} : Set E) ⊆ N := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    have hw0 : w = 0 := by simpa using hw
    rw [hw0]
    change z + 0 ∈ target
    simpa using hKtarget hz
  obtain ⟨V, W, _hVopen, hWopen, hKV, h0W, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hNopen hN
  have h0 : (0 : E) ∈ W := h0W (Set.mem_singleton 0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen 0 h0
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  let K' : Set E := ((fun p : E × E ↦ p.1 + p.2) ''
    (K ×ˢ Metric.closedBall (0 : E) r))
  have hK'compact : IsCompact K' := by
    dsimp [K']
    apply IsCompact.image
    · exact hK.prod (isCompact_closedBall _ _)
    · fun_prop
  have hK'subset : K' ⊆ target := by
    rintro q ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    have hwW : w ∈ W := by
      apply hball
      rw [Metric.mem_ball]
      have hw' : dist w 0 ≤ r := by simpa [Metric.mem_closedBall] using hw
      have : ‖w‖ < ε := by
        rw [dist_zero_right] at hw'
        dsimp [r] at *
        linarith
      simpa [dist_zero_right] using this
    have hp : (z, w) ∈ V ×ˢ W := ⟨hKV hz, hwW⟩
    exact hVW hp
  have hK'incl : K ⊆ K' := by
    intro z hz
    change z ∈ ((fun p : E × E ↦ p.1 + p.2) ''
      (K ×ˢ Metric.closedBall (0 : E) r))
    refine ⟨(z, 0), ⟨hz, Metric.mem_closedBall_self (le_of_lt hr)⟩, ?_⟩
    simp
  let δ : ℝ := ε / (2 * (1 + ‖v‖))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, K', hK'compact, hK'subset, hK'incl, ?_⟩
  intro h hh z hz
  change z + h • v ∈ ((fun p : E × E ↦ p.1 + p.2) ''
    (K ×ˢ Metric.closedBall (0 : E) r))
  refine ⟨(z, h • v), ⟨hz, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have hh' : |h| ≤ δ := hh.le
    dsimp [δ] at *
    calc
      |h| * ‖v‖ ≤ δ * ‖v‖ := mul_le_mul_of_nonneg_right hh' (norm_nonneg _)
      _ ≤ (ε / (2 * (1 + ‖v‖))) * (1 + ‖v‖) := by gcongr; linarith [norm_nonneg v]
      _ = ε / 2 := by field_simp
      _ ≤ ε / 2 := le_rfl
  · simp

section SecantData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem chartPrescribedData_differenceQuotient_uniform_holderBoundOn
    {G : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) (α : ℝ≥0) (hα : α ≤ 1) :
    ∃ δ C : ℝ≥0, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α C U (fun z =>
        (G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (z + h • v)) -
          G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) / h) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hOpen : IsOpen e.target := isOpen_extChartAt_target x
  obtain ⟨δ, hδ, K', hK', hK'S, hUK', hTranslate⟩ :=
    exists_compact_translated_chart_neighborhood (closure U) e.target hUcompact
      hUchart hOpen v
  let f : EuclideanSpace ℂ (Fin n) → ℝ := G ∘ e.symm
  have hGOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 G univ := by
    exact (contMDiffOn_univ.mpr hG).of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiffOn ℝ 2 f e.target := by
    exact (hGOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)).contDiffOn
  let D : ℝ≥0 := ⟨Metric.diam (closure U), Metric.diam_nonneg⟩
  have hD : ∀ z ∈ U, ∀ w ∈ U, edist z w ≤ D := by
    intro z hz w hw
    have hd := Metric.dist_le_diam_of_mem hUcompact.isBounded
      (subset_closure hz) (subset_closure hw)
    rw [edist_dist]
    have hd' : dist z w ≤ (D : ℝ) := hd
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hd'
  obtain ⟨C, hC⟩ := local_directionalQuotient_uniform_holderBoundOn_of_contDiffOn
    f e.target U K' hOpen hK' hK'S hf
    ((subset_closure : U ⊆ closure U).trans hUK') D α hα hD v δ hδ
    (fun h hh z hz => hTranslate h hh z (subset_closure hz))
  refine ⟨⟨δ, hδ.le⟩, C, hδ, ?_⟩
  intro h hne hh
  simpa only [f, e, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hC h hne hh

end SecantData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartBackgroundLogVolume_differenceQuotient_uniform_holderBoundOn
    (ω₀ : KahlerForm n M)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) (α : ℝ≥0) (hα : α ≤ 1) :
    ∃ δ C : ℝ≥0, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α C U (fun z =>
        (Real.log (RCLike.re (ω₀.metricInChart x (z + h • v)).det) -
          Real.log (RCLike.re (ω₀.metricInChart x z).det)) / h) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hOpen : IsOpen e.target := isOpen_extChartAt_target x
  obtain ⟨δ, hδ, Kbig, hKbig, hKbigS, hUKbig, hTranslate⟩ :=
    exists_compact_translated_chart_neighborhood (closure U) e.target hUcompact
      hUchart hOpen v
  let f : EuclideanSpace ℂ (Fin n) → ℝ :=
    fun z => Real.log (RCLike.re (ω₀.metricInChart x z).det)
  have hf : ContDiffOn ℝ 2 f e.target := by
    have hMetric : ContDiffOn ℝ 2 (fun z => ω₀.metricInChart x z) e.target := by
      apply contDiffOn_pi.mpr
      intro j
      apply contDiffOn_pi.mpr
      intro k
      exact (ω₀.contDiffOn_metricInChart x j k).of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    intro z hz
    have hMetricAt : ContDiffAt ℝ 2 (fun z => ω₀.metricInChart x z) z :=
      (hMetric z hz).contDiffAt (hOpen.mem_nhds hz)
    have hLog : ContDiffAt ℝ 2
        (fun A : Matrix (Fin n) (Fin n) ℂ => Real.log (RCLike.re A.det))
        (ω₀.metricInChart x z) := by
      exact (ω₀.posDef_metricInChart x hz).contDiffAt_log_det.of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    exact (hLog.comp z hMetricAt).contDiffWithinAt
  let D : ℝ≥0 := ⟨Metric.diam (closure U), Metric.diam_nonneg⟩
  have hD : ∀ z ∈ U, ∀ w ∈ U, edist z w ≤ D := by
    intro z hz w hw
    have hd := Metric.dist_le_diam_of_mem hUcompact.isBounded
      (subset_closure hz) (subset_closure hw)
    rw [edist_dist]
    have hdReal : dist z w ≤ (D : ℝ) := hd
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hdReal
  obtain ⟨C, hC⟩ :=
    local_directionalQuotient_uniform_holderBoundOn_of_contDiffOn f e.target U Kbig
      hOpen hKbig hKbigS hf ((subset_closure : U ⊆ closure U).trans hUKbig) D α hα hD v δ hδ
      (fun h hh z hz => hTranslate h hh z (subset_closure hz))
  refine ⟨⟨δ, hδ.le⟩, C, hδ, ?_⟩
  intro h hne hh
  simpa only [f, smul_eq_mul, div_eq_mul_inv, mul_comm] using hC h hne hh

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartBackgroundMetric_differenceQuotient_uniform_holderBoundOn
    (ω₀ : KahlerForm n M)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) (α : ℝ≥0) (hα : α ≤ 1) :
    ∃ δ C : ℝ≥0, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α C U (fun z =>
        h⁻¹ • (ω₀.metricInChart x (z + h • v) - ω₀.metricInChart x z)) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hOpen : IsOpen e.target := isOpen_extChartAt_target x
  obtain ⟨δ, hδ, Kbig, hKbig, hKbigS, hUKbig, hTranslate⟩ :=
    exists_compact_translated_chart_neighborhood (closure U) e.target hUcompact
      hUchart hOpen v
  have hf : ContDiffOn ℝ 2 (fun z => ω₀.metricInChart x z) e.target := by
    apply contDiffOn_pi.mpr
    intro j
    apply contDiffOn_pi.mpr
    intro k
    exact (ω₀.contDiffOn_metricInChart x j k).of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  let D : ℝ≥0 := ⟨Metric.diam (closure U), Metric.diam_nonneg⟩
  have hD : ∀ z ∈ U, ∀ w ∈ U, edist z w ≤ D := by
    intro z hz w hw
    have hd := Metric.dist_le_diam_of_mem hUcompact.isBounded
      (subset_closure hz) (subset_closure hw)
    rw [edist_dist]
    have hdReal : dist z w ≤ (D : ℝ) := hd
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hdReal
  obtain ⟨C, hC⟩ :=
    local_directionalQuotient_uniform_holderBoundOn_of_contDiffOn
      (fun z => ω₀.metricInChart x z) e.target U Kbig hOpen hKbig hKbigS hf
      ((subset_closure : U ⊆ closure U).trans hUKbig)
      D α hα hD v δ hδ
      (fun h hh z hz => hTranslate h hh z (subset_closure hz))
  exact ⟨⟨δ, hδ.le⟩, C, hδ, hC⟩

private theorem chartDifferenceQuotientRhs_uniform_holderBoundOn_of_components
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (G φ : M → ℝ) (x : M)
    (U : Set (EuclideanSpace ℂ (Fin n)))
    (v : EuclideanSpace ℂ (Fin n)) (α δ CG CL CA CB : ℝ≥0)
    (hG : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α CG U (fun z =>
        (G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (z + h • v)) -
          G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) / h))
    (hLog : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α CL U (fun z =>
        (Real.log (RCLike.re (ω₀.metricInChart x (z + h • v)).det) -
          Real.log (RCLike.re (ω₀.metricInChart x z).det)) / h))
    (hA : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α CA U (averagedChartInverse ω₀ φ x v h))
    (hB : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α CB U (fun z =>
        h⁻¹ • (ω₀.metricInChart x (z + h • v) - ω₀.metricInChart x z))) :
    ∃ C : ℝ≥0, ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α C U (chartDifferenceQuotientRhs ω₀ G φ x v h) := by
  obtain ⟨CT, hCT⟩ := CalabiYau.Schauder.holderBoundOn_zero_realTraceMatrixProduct n U α CA CB
  refine ⟨CG + CL + CT, ?_⟩
  intro h hne hh
  have hTrace := hCT _ _ (hA h hne hh) (hB h hne hh)
  have hBound := CalabiYau.Schauder.holderBoundOn_zero_sub
    (CalabiYau.Schauder.holderBoundOn_zero_add (hG h hne hh) (hLog h hne hh)) hTrace
  have hMatrix (z : EuclideanSpace ℂ (Fin n)) :
      chartMatrixDifferenceQuotient (ω₀.metricInChart x z)
          (ω₀.metricInChart x (z + h • v)) h =
        h⁻¹ • (ω₀.metricInChart x (z + h • v) - ω₀.metricInChart x z) := by
    ext i j
    simp only [chartMatrixDifferenceQuotient, Matrix.smul_apply, Matrix.sub_apply,
      Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  convert hBound using 1
  funext z
  simp only [chartDifferenceQuotientRhs, hMatrix]
  ring

/-- Entrywise averaged-inverse bounds suffice for the corrected RHS after shrinking the step
radius. No extra regularity of `φ` is needed for this conditional forcing estimate. -/
theorem exists_uniform_chartDifferenceQuotientRhs_holderBoundOn_of_average
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) {G : M → ℝ} (φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n))
    (α : ℝ≥0) (hα₁ : α < 1)
    (δA CA : ℝ≥0) (hδA : 0 < δA)
    (hAverageEntry : ∀ h : ℝ, h ≠ 0 → |h| < (δA : ℝ) →
      ∀ i j : Fin n,
        HolderBoundOn 0 α CA U
          (fun z ↦ averagedChartInverse ω₀ φ x v h z i j)) :
    ∃ δ Krhs : ℝ≥0, 0 < δ ∧ δ ≤ δA ∧
      ∀ h : ℝ, h ≠ 0 → |h| < (δ : ℝ) →
        (∀ z ∈ U, z + h • v ∈
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) ∧
        HolderBoundOn 0 α Krhs U
          (chartDifferenceQuotientRhs ω₀ G φ x v h) := by
      let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
      have hOpen : IsOpen e.target := isOpen_extChartAt_target x
      obtain ⟨δbuf, hδbuf, K', hK'compact, hK'target, hUK', hTranslate⟩ :=
        exists_compact_translated_chart_neighborhood (closure U) e.target hUcompact
          hUchart hOpen v
      let δbufN : ℝ≥0 := ⟨δbuf, le_of_lt hδbuf⟩
      have hα : α ≤ 1 := le_of_lt hα₁
      obtain ⟨δG, CG, hδG, hGholder⟩ :=
        chartPrescribedData_differenceQuotient_uniform_holderBoundOn hG x U
          hUcompact hUchart v α hα
      obtain ⟨δL, CL, hδL, hLholder⟩ :=
        chartBackgroundLogVolume_differenceQuotient_uniform_holderBoundOn ω₀ x U
          hUcompact hUchart v α hα
      obtain ⟨δB, CB, hδB, hBholder⟩ :=
        chartBackgroundMetric_differenceQuotient_uniform_holderBoundOn ω₀ x U
          hUcompact hUchart v α hα
      let δ : ℝ≥0 := min δA (min δG (min δL (min δB δbufN)))
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min hδA (lt_min hδG (lt_min hδL (lt_min hδB hδbuf)))
      have hδA' : δ ≤ δA := by
        dsimp [δ]
        exact min_le_left _ _
      have hδG' : δ ≤ δG := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hδL' : δ ≤ δL := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      have hδB' : δ ≤ δB := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hδbuf' : δ ≤ δbufN := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      have hAverageMatrix : ∀ h : ℝ, h ≠ 0 → |h| < (δ : ℝ) →
          HolderBoundOn 0 α CA U (averagedChartInverse ω₀ φ x v h) := by
        intro h hne hh
        apply holderBoundOn_zero_matrix_of_entrywise
        intro i j
        apply hAverageEntry h hne
        exact lt_of_lt_of_le hh (NNReal.coe_le_coe.mpr hδA')
      obtain ⟨C, hComponents⟩ :=
        chartDifferenceQuotientRhs_uniform_holderBoundOn_of_components ω₀ G φ x U v α δ
          CG CL CA CB
          (by
            intro h hne hh
            exact hGholder h hne
              (lt_of_lt_of_le hh (NNReal.coe_le_coe.mpr hδG')))
          (by
            intro h hne hh
            exact hLholder h hne
              (lt_of_lt_of_le hh (NNReal.coe_le_coe.mpr hδL')))
          (by
            intro h hne hh
            exact hAverageMatrix h hne hh)
          (by
            intro h hne hh
            exact hBholder h hne
              (lt_of_lt_of_le hh (NNReal.coe_le_coe.mpr hδB')))
      refine ⟨δ, C, hδ, hδA', ?_⟩
      intro h hne hh
      constructor
      · intro z hz
        have hz' : z ∈ closure U := subset_closure hz
        have hhbuf : |h| < δbuf :=
          lt_of_lt_of_le hh (NNReal.coe_le_coe.mpr hδbuf')
        exact hK'target (hTranslate h hhbuf z hz')
      · exact hComponents h hne hh

end KahlerForm
