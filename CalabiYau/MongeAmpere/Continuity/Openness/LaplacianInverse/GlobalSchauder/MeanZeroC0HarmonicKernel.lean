module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.LocalEstimate
import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.MaximumPrinciple.StrongMaximum
import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.MaximumPrinciple.ChartCoefficients

/-!
# C² harmonic mean-zero rigidity

The strong maximum principle for the uniformly elliptic complex Laplacian makes a C² harmonic
function constant on a connected manifold. Positive total Kähler volume and zero mean then
make the constant zero. In complex dimension zero, connectedness and nonemptiness reduce the
argument to the single-point case instead of invoking a positive-dimensional PDE theorem.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open MeasureTheory ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem hIsOneOne_c2 (φ : M → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ) :
    (mddbar n φ).IsOneOne := by
  intro x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm (e x) := by
    exact ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (φ ∘ e.symm) (e x) := (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) :=
    (contMDiffAt_iff_contDiffAt).mp hφM
  change (ddbar (φ ∘ e.symm) (e x)).IsOneOne
  exact isOneOne_ddbar hφC

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The intrinsic Kähler Laplacian in an arbitrary real chart, at C² regularity. This is the
coordinate bridge used for the C² compactness limit; it does not upgrade that limit to smoothness. -/
private theorem hLaplacianChart_c2 (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₁.laplacian f y = RCLike.re
      ((ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))⁻¹ *
        complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).trace := by
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := ψ y
  have hy' : y ∈ ψ.source := by simpa [ψ, ← extChartAt_source] using hy
  have hz : z ∈ ψ.target := ψ.map_source hy'
  have hzpoint : ψ.symm z = y := ψ.left_inv hy'
  have hychart : y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hy
  have hyCy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hOverlap : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hy', hychart⟩
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
      invFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
      left_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
          exact ⟨⟨hyC, hyCy⟩, hyC⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := x) (z := y) hyC
      right_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
          exact ⟨⟨hyCy, hyC⟩, hyCy⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := y) (z := y) (by simp)
      map_add' := by intro u v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_add u v
      map_smul' := by intro c v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_smul c v
    }
    continuous_toFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).continuous
    continuous_invFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y).continuous
  }
  have hA : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    have hdef : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
      rw [tangentCoordChange_def]
      simp [z, ψ]
    calc
      _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hdef.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hOverlap
      _ = _ := rfl
  have hrep (β : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      β.chartRep x z = (β y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp (x := x) (x' := y) (z := z) hz]
    · rw [hzpoint, FormField.chartRep_self, hA]
    · have heq : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z = y := by
        simpa [ψ] using hzpoint
      rw [heq]
      exact hychart
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₁.isOneOne y) (hIsOneOne_c2 f hf y) A
  have hddbar := chartRep_mddbar_of_contMDiff_two hf x hz
  calc
    ω₁.laplacian f y = relTrace (ω₁ y) (mddbar n f y) := rfl
    _ = relTrace ((ω₁ y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mddbar n f y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = RCLike.re
        ((ω₁.metricInChart x z)⁻¹ * complexHessian (f ∘ ψ.symm) z).trace := by
      rw [← hrep ω₁.toFormField, ← hrep (mddbar n f), hddbar]
      rfl

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem complexEllipticOp_eq_zero_of_laplacian_eq_zero_c2
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    (hLap : ω₁.laplacian f = 0) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    complexEllipticOp (fun w => (ω₁.metricInChart x w)⁻¹)
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z = 0 := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hy : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [e, ← extChartAt_source] using e.map_target hz
  have hchart := hLaplacianChart_c2 ω₁ f hf x hy
  rw [e.right_inv hz] at hchart
  have hzero : ω₁.laplacian f (e.symm z) = 0 := congrFun hLap (e.symm z)
  change RCLike.re ((ω₁.metricInChart x z)⁻¹ *
    complexHessian (f ∘ e.symm) z).trace = 0
  rw [← hchart]
  exact hzero

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem laplacian_nonpos_of_isLocalMax_c2 (ω₁ : KahlerForm n M)
    {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    {x : M} (hx : IsLocalMax f x) : ω₁.laplacian f x ≤ 0 := by
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := ψ x
  let f' := f ∘ ψ.symm
  have hcoord :=
    (contMDiffAt_iff_of_mem_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (I' := 𝓘(ℝ)) (x := x) (x' := x) (y := f x) (by simp) (by simp)).1 (hf x)
  have hC2 : ContDiffAt ℝ 2 f' z := by
    have h : ContDiffWithinAt ℝ 2 f' Set.univ z := by
      simpa [f', ψ, z, chartAt_self_eq, ModelWithCorners.range_eq_univ] using hcoord.2
    exact contDiffWithinAt_univ.mp h
  have hmax : IsLocalMax f' z := by
    have hx' : IsLocalMax f (ψ.symm z) := by simpa [ψ, z] using hx
    exact hx'.comp_continuous (continuousAt_extChartAt_symm x)
  have hnonneg : (-ddbar f' z).IsNonneg :=
    isNonneg_neg_ddbar_of_isLocalMax hC2 hmax
  have htrace : 0 ≤ relTrace (ω₁ x) (-ddbar f' z) :=
    ContinuousAlternatingMap.relTrace_nonneg (ω₁.isPositive x) hnonneg
  have htrace' : relTrace (ω₁ x) (ddbar f' z) ≤ 0 := by
    rw [ContinuousAlternatingMap.relTrace_neg] at htrace
    linarith
  simpa [KahlerForm.laplacian, mddbar, f', ψ, z] using htrace'

omit [ConnectedSpace M] in
private theorem eq_zero_of_eq_const_and_integral_zero [Nonempty M]
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hconst : ∃ c : ℝ, ∀ x, f x = c)
    (hMean : ∫ x, f x ∂ω₁.volume = 0) :
    ∀ x, f x = 0 := by
  classical
  obtain ⟨c, hc⟩ := hconst
  have hmass : 0 < ω₁.volume.real Set.univ := by
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact isOpen_univ.measure_ne_zero ω₁.volume
        ⟨Classical.choice ‹Nonempty M›, Set.mem_univ _⟩
    · exact measure_ne_top ω₁.volume Set.univ
  have hconstInt : ∫ x, f x ∂ω₁.volume = ω₁.volume.real Set.univ * c := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hc), integral_const]
    simp [MeasureTheory.measureReal_def, mul_comm]
  have hmul : ω₁.volume.real Set.univ * c = 0 := hconstInt.symm.trans hMean
  have hc0 : c = 0 := (mul_eq_zero.mp hmul).resolve_left hmass.ne'
  intro x
  rw [hc x, hc0]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Local strong maximum principle at a global maximum, assembled from the explicit C²
coordinate-domain theorem and local inverse-metric coefficient bounds. -/
private theorem eqOn_nhd_of_isGlobalMax_laplacian_eq_zero_c2 [Nonempty M]
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    (hLap : ω₁.laplacian f = 0) {x : M} (hmax : ∀ y, f y ≤ f x) :
    ∃ s ∈ 𝓝 x, ∀ y ∈ s, f y = f x := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  obtain ⟨r, lam, K, hr, hlam, hclosed, hEll, hbound⟩ :=
    ω₁.exists_chart_ball_inverse_metric_bounds x
  have hball : Metric.ball (e x) r ⊆ e.target :=
    fun z hz => hclosed (Metric.ball_subset_closedBall hz)
  have hC2 : ContDiffOn ℝ 2 (f ∘ e.symm) (Metric.ball (e x) r) := by
    intro z hz
    have hzTarget : z ∈ e.target := hball hz
    have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm z := by
      exact ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hzTarget)).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    exact ((contMDiffAt_iff_contDiffAt).mp
      ((hf (e.symm z)).comp z hsymm)).contDiffWithinAt
  have hconst : ∀ z ∈ Metric.ball (e x) r, (f ∘ e.symm) z = (f ∘ e.symm) (e x) := by
    apply eqOn_of_complexEllipticOp_nonneg_of_isMaxOn
      (fun w => (ω₁.metricInChart x w)⁻¹) Metric.isOpen_ball
      (convex_ball (e x) r).isPreconnected hC2 hlam hEll hbound
      (fun z hz => le_of_eq
        (complexEllipticOp_eq_zero_of_laplacian_eq_zero_c2 ω₁ f hf hLap x (hball hz)).symm)
      (Metric.mem_ball_self hr)
    intro z hz
    simpa [e] using hmax (e.symm z)
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r, ?_, ?_⟩
  · exact Filter.inter_mem
      ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))
      ((continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds (e x) hr))
  · intro y hy
    have h := hconst (e y) hy.2
    simpa only [Function.comp_apply, e.left_inv hy.1,
      e.left_inv (mem_extChartAt_source x)] using h

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] in
/-- The C² strong maximum-principle step: on a connected compact Kähler manifold, a C²
harmonic function is constant. This isolates the regularity-level gap that cannot be discharged
by the imported smooth-only harmonic rigidity theorem. -/
private theorem exists_eq_const_of_laplacian_eq_zero_c2 [Nonempty M]
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    (hLap : ω₁.laplacian f = 0) :
    ∃ c : ℝ, ∀ x, f x = c := by
  have hcont : Continuous f := hf.continuous
  obtain ⟨x₀, -, hglobal⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hloc : ∀ x, f x = f x₀ → ∃ s ∈ 𝓝 x, ∀ y ∈ s, f y = f x := by
    intro x hx
    apply eqOn_nhd_of_isGlobalMax_laplacian_eq_zero_c2 ω₁ f hf hLap
    intro y
    rw [hx]
    exact hglobal (Set.mem_univ y)
  let S : Set M := {x | f x = f x₀}
  have hSclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨s, hs, hlocx⟩ := hloc x hx
    filter_upwards [hs] with y hy
    change f y = f x₀
    rw [hlocx y hy]
    exact hx
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ ⟨x₀, rfl⟩
  refine ⟨f x₀, ?_⟩
  intro x
  have hx : x ∈ S := by rw [hSuniv]; exact Set.mem_univ x
  exact hx

/-- The C² version of harmonic-kernel rigidity needed after C² Arzelà–Ascoli; the smooth-only
`KahlerForm.eq_const_of_laplacian_eq_zero` does not apply to this limit. -/
theorem eq_zero_of_C2_laplacian_eq_zero_and_integral_zero [Nonempty M]
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    (hLap : ω₁.laplacian f = 0) (hMean : ∫ x, f x ∂ω₁.volume = 0) :
    ∀ x, f x = 0 := by
  obtain ⟨c, hconst⟩ := exists_eq_const_of_laplacian_eq_zero_c2 ω₁ f hf hLap
  exact eq_zero_of_eq_const_and_integral_zero ω₁ f ⟨c, hconst⟩ hMean

end KahlerForm
