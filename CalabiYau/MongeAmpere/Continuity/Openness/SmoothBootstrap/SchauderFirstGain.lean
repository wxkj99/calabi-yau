module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientEquation
import CalabiYau.Analysis.Holder.Compactness

/-!
# The initial regularity gain

Apply interior Schauder to each nonzero `C²` difference quotient on nested chart domains, with
uniform constants.  Compactness gives limits of the quotient Hessians; the derivative-limit
argument identifies the limit as the first derivative of the original potential and proves it is
`C²`.  Thus the initial `C²` solution gains one derivative without assuming its first derivative
is already a legal Schauder input.
-/

@[expose] public section

open Filter
open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Apply the `k = 0` Schauder estimate to a single quotient equation.  The uniformity in the
step size belongs to the caller: it is expressed by using the same `lam`, `K`, `K₁`, and domains
for every nonzero quotient. -/
private theorem contDiffOn_zero_of_holderBoundOn_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} (hα : 0 < α) {U : Set E} {f : E → F}
    (hf : HolderBoundOn 0 α C U f) : ContDiffOn ℝ 0 f U := by
  apply contDiffOn_zero.mpr
  let e := continuousMultilinearCurryFin0 ℝ E F
  have hcont := hf.2.continuousOn hα
  have htemp : ContinuousOn (fun z ↦ e (iteratedFDeriv ℝ 0 f z)) U :=
    e.continuous.continuousOn.comp hcont (Set.mapsTo_univ _ _)
  have heq : (fun z ↦ e (iteratedFDeriv ℝ 0 f z)) = f := by
    funext z
    simp [iteratedFDeriv_zero_eq_comp, e]
  rw [← heq]
  exact htemp

private theorem interiorSchauder_holderBoundOn_two
    (hSch : InteriorSchauderEstimate n) {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam K : ℝ≥0} (hlam : 0 < lam)
    {U V : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (hA : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ 2 u U)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hAHolder : ∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l)
    (K₀ K₁ : ℝ≥0)
    (hLu : ContDiffOn ℝ 0 (complexEllipticOp A u) U)
    (hLuHolder : HolderBoundOn 0 α K₁ U (complexEllipticOp A u))
    (huBound : ∀ z ∈ U, |u z| ≤ K₀) :
    ∃ C' : ℝ≥0, ContDiffOn ℝ 2 u U ∧ HolderBoundOn 2 α C' V u := by
  obtain ⟨C, hC⟩ := hSch 0 α hα₀ hα₁ lam K hlam U V hU hV hVU
  obtain ⟨hregular, hHolder⟩ := hC A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
  exact ⟨C * (K₁ + K₀), hregular, hHolder⟩

/-- Apply the same interior Schauder estimate to every member of a family of quotient equations.
Because its constant depends only on the fixed domains, ellipticity and coefficient bound, the
resulting `C^{2,α}` bound is independent of the nonzero step. -/
private theorem uniform_interiorSchauder_holderBoundOn_two
    (hSch : InteriorSchauderEstimate n) {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam K : ℝ≥0} (hlam : 0 < lam)
    {U V : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (S : Set ℝ)
    (A : ℝ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (q : ℝ → EuclideanSpace ℂ (Fin n) → ℝ)
    (hA : ∀ h ∈ S, ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A h z j l) U)
    (hq : ∀ h ∈ S, ContDiffOn ℝ 2 (q h) U)
    (hEll : ∀ h ∈ S, IsUniformlyEllipticOn (A h) lam U)
    (hAHolder : ∀ h ∈ S, ∀ j l, HolderBoundOn 0 α K U fun z ↦ A h z j l)
    (K₀ K₁ : ℝ≥0)
    (R : ℝ → EuclideanSpace ℂ (Fin n) → ℝ)
    (hRHolder : ∀ h ∈ S, HolderBoundOn 0 α K₁ U (R h))
    (hEq : ∀ h ∈ S, ∀ z ∈ U,
      complexEllipticOp (A h) (q h) z = R h z)
    (hqBound : ∀ h ∈ S, ∀ z ∈ U, |q h z| ≤ K₀) :
    ∃ C' : ℝ≥0, ∀ h ∈ S,
      ContDiffOn ℝ 2 (q h) U ∧ HolderBoundOn 2 α C' V (q h) := by
  obtain ⟨C, hC⟩ := hSch 0 α hα₀ hα₁ lam K hlam U V hU hV hVU
  refine ⟨C * (K₁ + K₀), ?_⟩
  intro h hh
  have hIter (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      iteratedFDeriv ℝ 0 (complexEllipticOp (A h) (q h)) z =
        iteratedFDeriv ℝ 0 (R h) z := by
    simp [iteratedFDeriv_zero_eq_comp, hEq h hh z hz]
  have hLqHolder : HolderBoundOn 0 α K₁ U (complexEllipticOp (A h) (q h)) := by
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hj0 : j = 0 := by omega
      subst j
      rw [hIter z hz]
      exact (hRHolder h hh).1 0 le_rfl z hz
    · intro z hz w hw
      rw [hIter z hz, hIter w hw]
      exact (hRHolder h hh).2 z hz w hw
  have hLq : ContDiffOn ℝ 0 (complexEllipticOp (A h) (q h)) U :=
    contDiffOn_zero_of_holderBoundOn_zero hα₀ hLqHolder
  obtain ⟨hregular, hHolder⟩ := hC (A h) (q h) (hA h hh) (hq h hh)
    (hEll h hh) (hAHolder h hh) K₀ K₁ hLq hLqHolder (hqBound h hh)
  exact ⟨hregular, hHolder⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in

/-- A chartwise first-derivative bound controls all small difference quotients whose connecting
segments stay in the compact chart piece. -/
private theorem differenceQuotient_abs_bound_of_chartHolderGauge
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (i : cover.ι) (α : ℝ≥0) {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (v : EuclideanSpace ℂ (Fin n)) (U : Set (EuclideanSpace ℂ (Fin n)))
    (δ : ℝ≥0)
    (hsegments : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U,
      segment ℝ z (z + h • v) ⊆ cover.piece i) :
    ∃ B : ℝ≥0, ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U,
      |((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
        (z + h • v) -
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z) / h|
          ≤ B * ‖v‖ := by
  obtain ⟨C, hC⟩ := (finiteChartHolderGauge_lt_top_iff cover 2 α φ).mp hφGauge
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let f := φ ∘ e.symm
  have hopen : IsOpen e.target := isOpen_extChartAt_target (cover.base i)
  have hf : ContDiffOn ℝ 2 f e.target := by
    have h := (contMDiff_iff.mp hφ).2 (cover.base i) 0
    simpa [f, e, extChartAt, chartAt_self_eq] using h
  have hHolder := hC i
  refine ⟨C, ?_⟩
  intro h hne hh z hz
  have hseg := hsegments h hne hh z hz
  have hdifferentiable (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ segment ℝ z (z + h • v)) :
      DifferentiableAt ℝ f y := by
    have hyTarget : y ∈ e.target := cover.piece_in_target i (hseg hy)
    exact ((hf y hyTarget).contDiffAt (hopen.mem_nhds hyTarget)).differentiableAt (by norm_num)
  have hderivBound (y : EuclideanSpace ℂ (Fin n))
      (hy : y ∈ segment ℝ z (z + h • v)) : ‖fderiv ℝ f y‖ ≤ C := by
    have hyTarget : y ∈ e.target := cover.piece_in_target i (hseg hy)
    calc
      ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ := (norm_iteratedFDeriv_one f).symm
      _ ≤ C := hHolder.1 1 (by norm_num) y (hseg hy)
  have hmv := (convex_segment z (z + h • v)).norm_image_sub_le_of_norm_fderiv_le
    hdifferentiable hderivBound (left_mem_segment ℝ z (z + h • v))
      (right_mem_segment ℝ z (z + h • v))
  have hnum : |f (z + h • v) - f z| ≤ C * (|h| * ‖v‖) := by
    rw [← Real.norm_eq_abs]
    calc
      ‖f (z + h • v) - f z‖ ≤ C * ‖(z + h • v) - z‖ := hmv
      _ = C * (|h| * ‖v‖) := by simp [norm_smul, Real.norm_eq_abs]
  rw [abs_div]
  calc
    |f (z + h • v) - f z| / |h| ≤ (C * (|h| * ‖v‖)) / |h| :=
      div_le_div_of_nonneg_right hnum (abs_nonneg h)
    _ = C * ‖v‖ := by
      field_simp [ne_of_gt (abs_pos.mpr hne)]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in

/-- A point in the interior of a relatively compact chart piece has nested ball domains on which
all sufficiently small difference-quotient segments remain in that piece. -/
private theorem exists_nested_chart_balls
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (z₀ v : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ interior (cover.piece i)) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      IsOpen (Metric.ball z₀ (r / 2)) ∧
      IsCompact (closure (Metric.ball z₀ (r / 2))) ∧
      closure (Metric.ball z₀ (r / 2)) ⊆ cover.piece i ∧
      IsCompact (closure (Metric.closedBall z₀ (r / 4))) ∧
      closure (Metric.closedBall z₀ (r / 4)) ⊆ Metric.ball z₀ (r / 2) ∧
      ∀ h : ℝ, |h| < δ → ∀ z ∈ Metric.ball z₀ (r / 2),
        segment ℝ z (z + h • v) ⊆ cover.piece i := by
  have hopen : IsOpen (interior (cover.piece i)) := isOpen_interior
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  let δ : ℝ := r / (4 * (1 + ‖v‖))
  have hδ : 0 < δ := by positivity
  have hδv : δ * ‖v‖ ≤ r / 4 := by
    have hratio : ‖v‖ / (1 + ‖v‖) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [norm_nonneg v]
    dsimp [δ]
    calc
      r / (4 * (1 + ‖v‖)) * ‖v‖ = (r / 4) * (‖v‖ / (1 + ‖v‖)) := by
        field_simp
      _ ≤ r / 4 := by
        calc
          (r / 4) * (‖v‖ / (1 + ‖v‖)) ≤ (r / 4) * 1 :=
            mul_le_mul_of_nonneg_left hratio (show 0 ≤ r / 4 by positivity)
          _ = r / 4 := by ring
  refine ⟨r, δ, hr, hδ, Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_⟩
  · have hcompact : IsCompact (Metric.closedBall z₀ (r / 2)) := isCompact_closedBall _ _
    apply hcompact.of_isClosed_subset isClosed_closure
    exact Metric.closure_ball_subset_closedBall
  · intro z hz
    have hzclosed : z ∈ Metric.closedBall z₀ (r / 2) :=
      Metric.closure_ball_subset_closedBall hz
    have hzball : z ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hzclosed) (by linarith)
    have hzinterior : z ∈ interior (cover.piece i) := hball hzball
    exact interior_subset hzinterior
  · have hVclosed : IsClosed (Metric.closedBall z₀ (r / 4)) := Metric.isClosed_closedBall
    rw [hVclosed.closure_eq]
    exact isCompact_closedBall _ _
  · have hVclosed : IsClosed (Metric.closedBall z₀ (r / 4)) := Metric.isClosed_closedBall
    rw [hVclosed.closure_eq]
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hz (by linarith)
  · intro h hh z hz
    have hz' : dist z z₀ < r / 2 := Metric.mem_ball.mp hz
    have hzball : z ∈ Metric.ball z₀ r :=
      Metric.mem_ball.mpr (lt_trans hz' (by linarith))
    have hdisp : |h| * ‖v‖ ≤ r / 4 := by
      calc
        |h| * ‖v‖ ≤ δ * ‖v‖ := mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg v)
        _ ≤ r / 4 := hδv
    have hendpoint : z + h • v ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsplit : z + h • v - z₀ = (z - z₀) + h • v := by abel
      rw [hsplit]
      calc
        ‖z - z₀ + h • v‖ ≤ ‖z - z₀‖ + ‖h • v‖ := norm_add_le _ _
        _ < r / 2 + r / 4 := by
          apply add_lt_add_of_lt_of_le (by simpa [dist_eq_norm] using hz')
          simpa [norm_smul, Real.norm_eq_abs, mul_comm] using hdisp
        _ < r := by linarith
    have hsegment : segment ℝ z (z + h • v) ⊆ Metric.ball z₀ r :=
      (convex_ball z₀ r).segment_subset hzball hendpoint
    exact hsegment.trans (hball.trans interior_subset)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in

/-- On a fixed nested chart domain, the exact quotient equations and common coefficient bounds
supply the hypotheses of the uniform Schauder-family estimate. Positive-exponent Hölder bounds
already give coefficient continuity. A chart-gauge first-derivative bound gives the uniform
quotient supremum when each connecting segment stays in the compact chart piece. -/
private theorem local_differenceQuotient_schauder_bound
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ} (hExact : HasExactDifferenceQuotientData ω₀ G φ)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hU : IsOpen U) (hUcompact : IsCompact (closure U))
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (V : Set (EuclideanSpace ℂ (Fin n))) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (hx : x = cover.base i)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (v : EuclideanSpace ℂ (Fin n)) (δ lam K : ℝ≥0)
    (hsegments : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U,
      segment ℝ z (z + h • v) ⊆ cover.piece i)
    (hlam : 0 < lam)
    (hStepBounds : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      (∀ z ∈ U, z + h • v ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) →
        IsUniformlyEllipticOn (averagedChartInverse ω₀ φ x v h) lam U ∧
          (∀ j l, HolderBoundOn 0 α K U fun z ↦ averagedChartInverse ω₀ φ x v h z j l) ∧
          HolderBoundOn 0 α K U (chartDifferenceQuotientRhs ω₀ G φ x v h)) :
    ∃ C' : ℝ≥0, ∀ h : ℝ, h ≠ 0 → |h| < δ →
      (∀ z ∈ U, z + h • v ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) →
      ContDiffOn ℝ 2
          (fun z ↦ ((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (z + h • v) -
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) / h) U ∧
        HolderBoundOn 2 α C' V
          (fun z ↦ ((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (z + h • v) -
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) / h) := by
  subst x
  obtain ⟨B, hB⟩ := differenceQuotient_abs_bound_of_chartHolderGauge cover i α hφ
    hφGauge v U δ hsegments
  let K₀ : ℝ≥0 := B * ‖v‖₊
  have hqBound : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      (∀ z ∈ U, z + h • v ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target) →
      ∀ z ∈ U,
        |((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
            (z + h • v) -
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z) / h| ≤ K₀ := by
    intro h hne hsmall htrans z hz
    have hb := hB h hne hsmall z hz
    have hconst : (B : ℝ) * ‖v‖ = (K₀ : ℝ) := by
      simp [K₀]
    exact hb.trans_eq hconst
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let q : ℝ → EuclideanSpace ℂ (Fin n) → ℝ := fun h z ↦
    ((φ ∘ e.symm) (z + h • v) - (φ ∘ e.symm) z) / h
  let A : ℝ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun h z ↦ averagedChartInverse ω₀ φ (cover.base i) v h z
  let R : ℝ → EuclideanSpace ℂ (Fin n) → ℝ :=
    fun h z ↦ chartDifferenceQuotientRhs ω₀ G φ (cover.base i) v h z
  let S : Set ℝ := {h | h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target}
  have hq : ∀ h ∈ S, ContDiffOn ℝ 2 (q h) U := by
    intro h hh
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    simpa [q, e] using (hExact (cover.base i) U hU hUcompact hUtarget v h hs.1 hs.2.2).1
  have hA : ∀ h ∈ S, ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A h z j l) U := by
    intro h hh j l
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    apply contDiffOn_zero_of_holderBoundOn_zero hα₀
    simpa [A] using (hStepBounds h hs.1 hs.2.1 hs.2.2).2.1 j l
  have hEll : ∀ h ∈ S, IsUniformlyEllipticOn (A h) lam U := by
    intro h hh
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    simpa [A] using (hStepBounds h hs.1 hs.2.1 hs.2.2).1
  have hAHolder : ∀ h ∈ S, ∀ j l, HolderBoundOn 0 α K U fun z ↦ A h z j l := by
    intro h hh j l
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    simpa [A] using (hStepBounds h hs.1 hs.2.1 hs.2.2).2.1 j l
  have hRHolder : ∀ h ∈ S, HolderBoundOn 0 α K U (R h) := by
    intro h hh
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    simpa [R] using (hStepBounds h hs.1 hs.2.1 hs.2.2).2.2
  have hEq : ∀ h ∈ S, ∀ z ∈ U, complexEllipticOp (A h) (q h) z = R h z := by
    intro h hh z hz
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    simpa [A, q, R, e] using
      (hExact (cover.base i) U hU hUcompact hUtarget v h hs.1 hs.2.2).2.2 z hz
  have hqBound' : ∀ h ∈ S, ∀ z ∈ U, |q h z| ≤ K₀ := by
    intro h hh z hz
    have hs : h ≠ 0 ∧ |h| < δ ∧ ∀ z ∈ U, z + h • v ∈ e.target := by
      simpa [S] using hh
    simpa [q, e] using hqBound h hs.1 hs.2.1 hs.2.2 z hz
  obtain ⟨C', hC'⟩ := uniform_interiorSchauder_holderBoundOn_two hSch
    hα₀ hα₁ hlam hU hV hVU S A q hA hq hEll hAHolder K₀ K R hRHolder hEq hqBound'
  refine ⟨C', ?_⟩
  intro h hne hsmall htrans
  have hh : h ∈ S := by
    simp only [S, Set.mem_ofPred_eq]
    exact ⟨hne, hsmall, htrans⟩
  simpa [q, e] using hC' h hh

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in

/-- Package the local nested-domain construction with the exact difference-quotient data. This
produces the uniform `C^{2,α}` quotient family on a smaller chart ball at every point of a compact
chart piece. -/
private theorem exists_local_differenceQuotient_schauder_bound
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hData : HasDifferenceQuotientSchauderData ω₀ G φ α)
    (i : cover.ι) (z₀ : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ interior (cover.piece i)) (v : EuclideanSpace ℂ (Fin n)) :
    ∃ (U V : Set (EuclideanSpace ℂ (Fin n))) (δ C : ℝ≥0),
      0 < δ ∧ IsOpen U ∧ IsCompact (closure U) ∧
      closure U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
      IsCompact (closure V) ∧ closure V ⊆ U ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ → (∀ z ∈ U, z + h • v ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target) →
        let q : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
          ((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
            (z + h • v) -
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z) / h
        ContDiffOn ℝ 2 q U ∧ HolderBoundOn 2 α C V q := by
  rcases hData with ⟨hExact, hUniform⟩
  obtain ⟨r, δgeo, _hr, hδgeo, hU, hUcompact, hUpiece, hV, hVU, hsegments⟩ :=
    exists_nested_chart_balls cover i z₀ v hz₀
  let U := Metric.ball z₀ (r / 2)
  let V := Metric.closedBall z₀ (r / 4)
  have hU' : IsOpen U := by simp [U]
  have hUcompact' : IsCompact (closure U) := by simpa [U] using hUcompact
  have hUpiece' : closure U ⊆ cover.piece i := by simpa [U] using hUpiece
  have hV' : IsCompact (closure V) := by simpa [V] using hV
  have hVU' : closure V ⊆ U := by simpa [U, V] using hVU
  have hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
    hUpiece'.trans (cover.piece_in_target i)
  obtain ⟨δdata, lam, K, hδdata, hlam, hBounds⟩ :=
    hUniform (cover.base i) U hU' hUcompact' hUtarget v
  let δgeoNN : ℝ≥0 := Real.toNNReal δgeo
  have hδgeoNN : (δgeoNN : ℝ) = δgeo := Real.coe_toNNReal δgeo hδgeo.le
  let δ : ℝ≥0 := min δgeoNN δdata
  have hδ : 0 < δ := lt_min (Real.toNNReal_pos.mpr hδgeo) hδdata
  have hsegments' : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U,
      segment ℝ z (z + h • v) ⊆ cover.piece i := by
    intro h hne hsmall z hz
    have hsmallGeo : |h| < δgeo := by
      calc
        |h| < (δ : ℝ) := hsmall
        _ ≤ δgeo := by rw [← hδgeoNN]; exact_mod_cast (min_le_left δgeoNN δdata)
    exact hsegments h hsmallGeo z hz
  have hStepBounds : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      (∀ z ∈ U, z + h • v ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target) →
        IsUniformlyEllipticOn (averagedChartInverse ω₀ φ (cover.base i) v h) lam U ∧
          (∀ j l, HolderBoundOn 0 α K U fun z ↦
            averagedChartInverse ω₀ φ (cover.base i) v h z j l) ∧
          HolderBoundOn 0 α K U
            (chartDifferenceQuotientRhs ω₀ G φ (cover.base i) v h) := by
    intro h hne hsmall htrans
    have hsmallData : |h| < (δdata : ℝ) := by
      calc
        |h| < (δ : ℝ) := hsmall
        _ ≤ δdata := by exact_mod_cast (min_le_right δgeoNN δdata)
    exact hBounds h hne hsmallData htrans
  obtain ⟨C, hC⟩ := local_differenceQuotient_schauder_bound hSch ω₀ α hα₀ hα₁
    hExact (cover.base i) U hU' hUcompact' hUtarget V hV' hVU' cover i rfl hφ hφGauge
    v δ lam K hsegments' hlam hStepBounds
  refine ⟨U, V, δ, C, hδ, hU', hUcompact', hUtarget, hV', hVU', ?_⟩
  intro h hne hsmall htrans
  simpa [U, V] using hC h hne hsmall htrans

/-- A common `C^{2,α}` bound on a compact domain gives a subsequence of quotient Hessians
converging uniformly there. The output is stated on the compact subtype so the published local
Arzelà–Ascoli theorem applies without extending the quotients outside the domain. -/
private theorem exists_subseq_tendstoUniformlyOn_quotient_hessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {V : Set E}
    (hV : IsCompact V) {α C : ℝ≥0} (hα : 0 < α)
    (q : ℕ → E → ℝ)
    (hqHolder : ∀ n, HolderBoundOn 2 α C V (q n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : V → (E [×2]→L[ℝ] ℝ),
      Continuous g ∧ TendstoUniformlyOn
        (fun n (z : V) ↦ iteratedFDeriv ℝ 2 (q (ψ n)) z.1)
        g Filter.atTop Set.univ := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : FiniteDimensional ℝ (E →L[ℝ] ℝ) := by infer_instance
  have : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := by infer_instance
  have : FiniteDimensional ℝ (E [×2]→L[ℝ] ℝ) :=
    (CalabiYau.Schauder.hessianCurryEquiv E ℝ).toLinearEquiv.symm.finiteDimensional
  let : ProperSpace (E [×2]→L[ℝ] ℝ) := FiniteDimensional.proper ℝ _
  let f : ℕ → E → (E [×2]→L[ℝ] ℝ) :=
    fun n z ↦ iteratedFDeriv ℝ 2 (q n) z
  have hholder : ∀ K : Set V, IsCompact K →
      ∃ C' : ℝ≥0, ∀ n,
        HolderOnWith C' α (fun z : V ↦ f n z.1) K := by
    intro K hK
    refine ⟨C, ?_⟩
    intro n
    have hn : HolderWith C α
        (V.domRestrict (iteratedFDeriv ℝ 2 (q n))) :=
      (HolderWith.restrict_iff).symm.mp (hqHolder n).2
    exact (hn.holderOnWith K).mono (by
      intro z hz
      exact hz)
  have hbound : ∀ z ∈ V, ∃ M : ℝ, ∀ n, ‖f n z‖ ≤ M := by
    intro z hz
    refine ⟨(C : ℝ), ?_⟩
    intro n
    exact_mod_cast (hqHolder n).1 2 (by norm_num) z hz
  obtain ⟨ψ, g, hψ, hg, hconv⟩ :=
    CalabiYau.Schauder.arzela_ascoli_subseq_tendsto_locally_uniformly_on_of_locally_holderOnWith
      (U := V) f hα hholder hbound
  refine ⟨ψ, hψ, g, hg, ?_⟩
  simpa [f] using hconv Set.univ isCompact_univ

/-- At each point, a nonzero scalar difference quotient along a fixed direction converges to the
Fréchet derivative in that direction. -/
private theorem quotient_tendsto_fderiv_along_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} {v : E}
    (hf : DifferentiableAt ℝ f x)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ k in atTop, h k ≠ 0) :
    Tendsto (fun k ↦ (h k)⁻¹ * (f (x + h k • v) - f x)) atTop
      (𝓝 (fderiv ℝ f x v)) := by
  let T : ℝ → E := fun t ↦ x + t • v
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hT : HasFDerivAt T L 0 := by
    dsimp [T, L]
    simpa [add_comm] using (hasFDerivAt_id (0 : ℝ)).smul_const v |>.const_add x
  have hTx : T 0 = x := by simp [T]
  have hf' : HasFDerivAt f (fderiv ℝ f (T 0)) (T 0) := by
    simpa [hTx] using hf.hasFDerivAt
  have hcomp0 : HasFDerivAt (f ∘ T) ((fderiv ℝ f (T 0)).comp L) 0 :=
    hf'.comp 0 hT
  have hcomp : HasFDerivAt (f ∘ T) ((fderiv ℝ f x).comp L) 0 := by
    simpa [T] using hcomp0
  have hrem := (hasFDerivAt_iff_tendsto.mp hcomp)
  have hrem' := hrem.comp hh
  have hquot : Tendsto
      (fun k ↦ ‖h k‖⁻¹ * ‖f (x + h k • v) - f x -
        (fderiv ℝ f x) (h k • v)‖) atTop (𝓝 0) := by
    simpa [T, Function.comp_def, L] using hrem'
  have hdiff : Tendsto
      (fun k ↦ ‖(h k)⁻¹ * (f (x + h k • v) - f x) - fderiv ℝ f x v‖) atTop (𝓝 0) := by
    refine hquot.congr' ?_
    filter_upwards [hne] with k hk
    have halg : (h k)⁻¹ * (f (x + h k • v) - f x) - fderiv ℝ f x v =
        (h k)⁻¹ * (f (x + h k • v) - f x - (fderiv ℝ f x) (h k • v)) := by
      rw [map_smul]
      simp only [smul_eq_mul]
      field_simp [hk]
    rw [halg, norm_mul, norm_inv]
  exact (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa using hdiff)

private theorem quotient_step_segments_in_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z₀ v : E) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    let η : ℝ := min δ (r / (8 * (1 + ‖v‖)));
    let h : ℕ → ℝ := fun k ↦ η / ((k : ℝ) + 2);
    ∀ k, ∀ z ∈ Metric.closedBall z₀ (r / 4),
      segment ℝ z (z + h k • v) ⊆ Metric.closedBall z₀ (r / 2) := by
  dsimp only
  intro k z hz
  have hη : 0 < min δ (r / (8 * (1 + ‖v‖))) := by positivity
  have hseq : 0 < min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2) :=
    div_pos hη (by positivity)
  have hdisp : (min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) * ‖v‖ ≤ r / 8 := by
    have hden : 1 < (k : ℝ) + 2 := by exact_mod_cast (show 1 < k + 2 by omega)
    have hstep : min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2) <
        min δ (r / (8 * (1 + ‖v‖))) := by
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith [hη]
    have hmin : min δ (r / (8 * (1 + ‖v‖))) ≤ r / (8 * (1 + ‖v‖)) := min_le_right _ _
    have hratio : ‖v‖ / (1 + ‖v‖) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [norm_nonneg v]
    calc
      min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2) * ‖v‖ ≤
          min δ (r / (8 * (1 + ‖v‖))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hstep) (norm_nonneg v)
      _ ≤ (r / (8 * (1 + ‖v‖))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hmin (norm_nonneg v)
      _ = (r / 8) * (‖v‖ / (1 + ‖v‖)) := by
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < 8 * (1 + ‖v‖))]
      _ ≤ r / 8 := by exact mul_le_of_le_one_right (by positivity) hratio
  have hz' : dist z z₀ ≤ r / 4 := Metric.mem_closedBall.mp hz
  have hright : z + (min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) • v ∈
      Metric.closedBall z₀ (r / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit : z + (min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) • v - z₀ =
        (z - z₀) + (min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) • v := by abel
    rw [hsplit]
    calc
      ‖z - z₀ + (min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) • v‖ ≤
          ‖z - z₀‖ + ‖(min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) • v‖ := norm_add_le _ _
      _ ≤ r / 4 + (min δ (r / (8 * (1 + ‖v‖))) / ((k : ℝ) + 2)) * ‖v‖ := by
        gcongr
        · simpa [dist_eq_norm] using hz'
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hseq]
      _ ≤ r / 4 + r / 8 := by nlinarith [hdisp]
      _ ≤ r / 2 := by nlinarith [hr]
  have hzleft : z ∈ Metric.closedBall z₀ (r / 2) := by
    rw [Metric.mem_closedBall]
    exact le_trans hz' (by linarith)
  exact (convex_closedBall z₀ (r / 2)).segment_subset hzleft hright

private theorem signed_translation_segment_subset_compact_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z₀ v : E) {r R S h : ℝ} (hrR : r < R) (hRS : R < S)
    (hdisp : |h| * ‖v‖ ≤ R - r) {z : E}
    (hz : z ∈ Metric.closedBall z₀ r) :
    segment ℝ z (z + h • v) ⊆ Metric.closedBall z₀ R ∧
      segment ℝ z (z + h • v) ⊆ Metric.ball z₀ S := by
  have hleft : z ∈ Metric.closedBall z₀ R := by
    rw [Metric.mem_closedBall]
    exact le_trans (Metric.mem_closedBall.mp hz) (le_of_lt hrR)
  have hright : z + h • v ∈ Metric.closedBall z₀ R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit : z + h • v - z₀ = (z - z₀) + h • v := by abel
    rw [hsplit]
    calc
      ‖z - z₀ + h • v‖ ≤ ‖z - z₀‖ + ‖h • v‖ := norm_add_le _ _
      _ ≤ r + |h| * ‖v‖ := by
        gcongr
        · simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
        · rw [norm_smul, Real.norm_eq_abs]
      _ ≤ R := by linarith [hrR, hdisp]
  have hsegment : segment ℝ z (z + h • v) ⊆ Metric.closedBall z₀ R :=
    (convex_closedBall z₀ R).segment_subset hleft hright
  refine ⟨hsegment, ?_⟩
  intro y hy
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt (Metric.mem_closedBall.mp (hsegment hy)) hRS

private theorem signed_quotient_tendsto_uniformlyOn_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U L K : Set E} (hU : IsOpen U) (hL : IsCompact L)
    (hLU : L ⊆ U) (hK : K ⊆ L)
    {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (v : E) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, h n ≠ 0)
    (hseg : ∀ n z, z ∈ K → segment ℝ z (z + h n • v) ⊆ L) :
    TendstoUniformlyOn
      (fun n z ↦ (f (z + h n • v) - f z) / h n)
      (fun z ↦ fderiv ℝ f z v) atTop K := by
  have hfdcont : ContinuousOn (fderiv ℝ f) L :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hLU
  have hfduniform : UniformContinuousOn (fderiv ℝ f) L :=
    hL.uniformContinuousOn_of_continuous hfdcont
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let η : ℝ := ε / (1 + ‖v‖)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hfdδ⟩ := (Metric.uniformContinuousOn_iff.mp hfduniform) η hη
  have ht : ∀ᶠ n in atTop, |h n| * ‖v‖ < δ := by
    have ht0 : Tendsto (fun n : ℕ ↦ |h n| * ‖v‖) atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using hh.norm.mul_const ‖v‖
    filter_upwards [Metric.tendsto_nhds.mp ht0 δ hδ] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [ht, hne] with n hn hne z hz
  have hclose (y : E) (hy : y ∈ segment ℝ z (z + h n • v)) :
      dist y z ≤ |h n| * ‖v‖ := by
    rw [dist_eq_norm]
    rw [segment_eq_image] at hy
    rcases hy with ⟨t, htmem, hty⟩
    have heq : y - z = t • (h n • v) := by
      rw [← hty]
      simp only [smul_add, sub_smul]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg htmem.1,
      norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left
      (mul_nonneg (abs_nonneg (h n)) (norm_nonneg v)) htmem.2
  let g : E → ℝ := fun y ↦ f y - fderiv ℝ f z y + fderiv ℝ f z z
  have hdiff (y : E) (hy : y ∈ segment ℝ z (z + h n • v)) : DifferentiableAt ℝ g y := by
    have hyL : y ∈ L := hseg n z hz hy
    have hyU : y ∈ U := hLU hyL
    have hfy := (hf y hyU).contDiffAt (hU.mem_nhds hyU)
    have hfg : DifferentiableAt ℝ f y := hfy.differentiableAt (by norm_num)
    dsimp [g]
    fun_prop
  have hderivBound (y : E) (hy : y ∈ segment ℝ z (z + h n • v)) :
      ‖fderiv ℝ g y‖ ≤ η := by
    have hyL : y ∈ L := hseg n z hz hy
    have hyclose := hclose y hy
    have hfd := hfdδ y hyL z (hK hz) (lt_of_le_of_lt hyclose hn)
    have hfy := (hf y (hLU hyL)).contDiffAt (hU.mem_nhds (hLU hyL))
    have hfAt : HasFDerivAt f (fderiv ℝ f y) y :=
      (hfy.differentiableAt (by norm_num)).hasFDerivAt
    have hlin : HasFDerivAt (fun w : E ↦ fderiv ℝ f z w - fderiv ℝ f z z)
        (fderiv ℝ f z) y := (fderiv ℝ f z).hasFDerivAt.sub_const _
    have hsub := hfAt.sub hlin
    have heq : (fun w ↦ f w - (fderiv ℝ f z w - fderiv ℝ f z z)) = g := by
      funext w
      simp [g]
      ring
    have hfdg : fderiv ℝ g y = fderiv ℝ f y - fderiv ℝ f z := by
      rw [congrArg (fun F : E → ℝ ↦ fderiv ℝ F y) heq.symm]
      exact hsub.fderiv
    rw [hfdg]
    exact le_of_lt (by simpa [dist_eq_norm, norm_sub_rev] using hfd)
  have hmv := (convex_segment z (z + h n • v)).norm_image_sub_le_of_norm_fderiv_le
    hdiff hderivBound (left_mem_segment ℝ z (z + h n • v))
      (right_mem_segment ℝ z (z + h n • v))
  have herror :
      |(f (z + h n • v) - f z) / h n - fderiv ℝ f z v| ≤ η * ‖v‖ := by
    let L₀ := fderiv ℝ f z
    have hlin : L₀ (z + h n • v) - L₀ z = h n * L₀ v := by
      rw [← map_sub]
      have hpoint : z + h n • v - z = h n • v := by module
      rw [hpoint, map_smul, smul_eq_mul]
    have hlin' : fderiv ℝ f z (z + h n • v) - fderiv ℝ f z z =
        h n * fderiv ℝ f z v := by simp [L₀] at hlin ⊢
    have hrewrite : g (z + h n • v) - g z =
        f (z + h n • v) - f z - h n * L₀ v := by
      calc
        g (z + h n • v) - g z =
            f (z + h n • v) - f z -
              (fderiv ℝ f z (z + h n • v) - fderiv ℝ f z z) := by
                dsimp [g]
                ring
        _ = f (z + h n • v) - f z - h n * L₀ v := by rw [hlin']
    have hnorm : ‖(z + h n • v) - z‖ = |h n| * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hnum : |f (z + h n • v) - f z - h n * L₀ v| ≤
        η * (|h n| * ‖v‖) := by
      calc
        |f (z + h n • v) - f z - h n * L₀ v| =
            ‖g (z + h n • v) - g z‖ := by rw [hrewrite, Real.norm_eq_abs]
        _ ≤ η * ‖(z + h n • v) - z‖ := hmv
        _ = η * (|h n| * ‖v‖) := by rw [hnorm]
    have halg : (f (z + h n • v) - f z) / h n - L₀ v =
        (f (z + h n • v) - f z - h n * L₀ v) / h n := by
      field_simp [hne]
    rw [halg, abs_div]
    have habspos : 0 < |h n| := abs_pos.mpr hne
    calc
      |f (z + h n • v) - f z - h n * L₀ v| / |h n| ≤
          (η * (|h n| * ‖v‖)) / |h n| :=
        div_le_div_of_nonneg_right hnum (le_of_lt habspos)
      _ = η * ‖v‖ := by field_simp [hne]
  have hηε : η * ‖v‖ < ε := by
    dsimp [η]
    have hv : 0 ≤ ‖v‖ := norm_nonneg v
    have hden : 0 < 1 + ‖v‖ := by positivity
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hden).2 (by nlinarith [hε, hv])
  have habs : |(f (z + h n • v) - f z) / h n - fderiv ℝ f z v| < ε :=
    lt_of_le_of_lt herror hηε
  simpa [Real.dist_eq, abs_sub_comm] using habs

private theorem lipschitzOnWith_firstJet_of_holderBoundOn_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hKconvex : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} {α C : ℝ≥0}
    (hsmooth : ContDiffOn ℝ 2 f U) (hbound : HolderBoundOn 2 α C K f) :
    LipschitzOnWith C (fun x ↦ iteratedFDeriv ℝ 1 f x) K := by
  have hdiff1lt : (↑(1 : ℕ) : ℕ∞ω) < (↑(2 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (show (1 : ℕ) < 2 by norm_num)
  have hdiff1 (x : E) (hx : x ∈ K) :
      DifferentiableAt ℝ (fun y ↦ iteratedFDeriv ℝ 1 f y) x :=
    (hsmooth.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt_iteratedFDeriv hdiff1lt
  apply hKconvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact hdiff1
  · intro x hx
    have hb : ‖fderiv ℝ (fun y ↦ iteratedFDeriv ℝ 1 f y) x‖ ≤ (C : ℝ) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound.1 2 le_rfl x hx
    exact_mod_cast hb

/-- A common `C^{2,α}` bound on a convex compact chart domain gives a subsequence whose quotient
first jets converge uniformly. This complements the Hessian subsequence above so the two derivative
limits can be identified on a smaller open ball. -/
private theorem exists_subseq_tendstoUniformlyOn_quotient_first_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V U : Set E} (hV : IsCompact V) (hVconvex : Convex ℝ V)
    (hU : IsOpen U) (hVU : V ⊆ U)
    {q : ℕ → E → ℝ} {α C : ℝ≥0}
    (hq : ∀ n, ContDiffOn ℝ 2 (q n) U)
    (hqHolder : ∀ n, HolderBoundOn 2 α C V (q n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : V → (E [×1]→L[ℝ] ℝ),
      Continuous g ∧ TendstoUniformly
        (fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q (ψ n)) z.1) g Filter.atTop := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : FiniteDimensional ℝ (E →L[ℝ] ℝ) := by infer_instance
  have : FiniteDimensional ℝ (E [×1]→L[ℝ] ℝ) :=
    (continuousMultilinearCurryFin1 ℝ E ℝ).toLinearEquiv.symm.finiteDimensional
  let : ProperSpace (E [×1]→L[ℝ] ℝ) := FiniteDimensional.proper ℝ _
  let fseq : ℕ → C(V, E [×1]→L[ℝ] ℝ) := fun n ↦ ⟨
    (fun z : V ↦ iteratedFDeriv ℝ 1 (q n) (z : E)),
    (lipschitzOnWith_iff_restrict.mp
      (lipschitzOnWith_firstJet_of_holderBoundOn_two hVconvex hU hVU
        (hq n) (hqHolder n))).continuous⟩
  have hLip (n : ℕ) : LipschitzWith C (fseq n : V → E [×1]→L[ℝ] ℝ) := by
    change LipschitzWith C (V.domRestrict (fun z ↦ iteratedFDeriv ℝ 1 (q n) z))
    exact (lipschitzOnWith_iff_restrict.mp
      (lipschitzOnWith_firstJet_of_holderBoundOn_two hVconvex hU hVU
        (hq n) (hqHolder n)))
  have hequi : Equicontinuous (fun n ↦ (fseq n : V → E [×1]→L[ℝ] ℝ)) :=
    (LipschitzWith.uniformEquicontinuous _ C hLip).equicontinuous
  have hbounded (z : V) : ∃ B : ℝ, ∀ n, ‖fseq n z‖ ≤ B := by
    refine ⟨C, ?_⟩
    intro n
    change ‖iteratedFDeriv ℝ 1 (q n) (z : E)‖ ≤ (C : ℝ)
    exact (hqHolder n).1 1 (by norm_num) z z.property
  obtain ⟨ψ, g, hψ, hconv⟩ :=
    CalabiYau.CheegerGromovCompactness.arzelaAscoli_subseq_vec fseq hequi hbounded
  refine ⟨ψ, hψ, g, g.continuous, ?_⟩
  change TendstoUniformly
    (fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q (ψ n)) (z : E))
    (fun z : V ↦ g z) Filter.atTop
  exact tendstoUniformlyOn_univ.mp (hconv Set.univ isCompact_univ)

private theorem tendstoLocallyUniformlyOn_of_uniformly_convergent_subtype
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {V W : Set E} {f : ℕ → E → F} {g : V → F} {gE : E → F}
    (hWV : W ⊆ V)
    (hgE : ∀ x (hx : x ∈ W), gE x = g ⟨x, hWV hx⟩)
    (hconv : TendstoUniformly (fun n (z : V) ↦ f n z.1) g atTop) :
    TendstoLocallyUniformlyOn f gE atTop W := by
  intro u hu x hx
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨W, eventually_mem_nhdsWithin, ?_⟩
  have hεconv := (Metric.tendstoUniformly_iff.mp hconv) ε hε
  filter_upwards [hεconv] with n hn y hy
  apply hεu
  simpa [hgE y hy, dist_comm] using hn ⟨y, hWV hy⟩

private theorem tendstoUniformly_comp_strictMono
    {X Y : Type*} [PseudoMetricSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {φ : ℕ → ℕ}
    (h : TendstoUniformly f g atTop) (hφ : StrictMono φ) :
    TendstoUniformly (fun n ↦ f (φ n)) g atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  exact hφ.tendsto_atTop (h ε hε)

/-- Diagonal compactness supplies one subsequence on which both the quotient gradients and Hessians
converge uniformly on the same compact convex chart domain. -/
private theorem exists_subseq_tendstoUniformlyOn_quotient_first_and_second_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V U : Set E} (hV : IsCompact V) (hVconvex : Convex ℝ V)
    (hU : IsOpen U) (hVU : V ⊆ U) {q : ℕ → E → ℝ} {α C : ℝ≥0} (hα : 0 < α)
    (hq : ∀ n, ContDiffOn ℝ 2 (q n) U)
    (hqHolder : ∀ n, HolderBoundOn 2 α C V (q n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ g : V → (E [×1]→L[ℝ] ℝ), Continuous g ∧
      ∃ H : V → (E [×2]→L[ℝ] ℝ), Continuous H ∧
        TendstoUniformly
          (fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q (ψ n)) z.1) g atTop ∧
        TendstoUniformly
          (fun n (z : V) ↦ iteratedFDeriv ℝ 2 (q (ψ n)) z.1) H atTop := by
  obtain ⟨φ₁, hφ₁, g, hg, hgrad⟩ :=
    exists_subseq_tendstoUniformlyOn_quotient_first_jet
      hV hVconvex hU hVU hq hqHolder
  let q' : ℕ → E → ℝ := fun n ↦ q (φ₁ n)
  have hq' (n : ℕ) : ContDiffOn ℝ 2 (q' n) U := hq (φ₁ n)
  have hqHolder' (n : ℕ) : HolderBoundOn 2 α C V (q' n) := hqHolder (φ₁ n)
  obtain ⟨φ₂, hφ₂, H, hH, hhess⟩ :=
    exists_subseq_tendstoUniformlyOn_quotient_hessian hV hα q' hqHolder'
  let ψ : ℕ → ℕ := φ₁ ∘ φ₂
  have hψ : StrictMono ψ := hφ₁.comp hφ₂
  have hgrad' := tendstoUniformly_comp_strictMono
    (f := fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q (φ₁ n)) z.1) hgrad hφ₂
  have hhessUniform : TendstoUniformly
      (fun n (z : V) ↦ iteratedFDeriv ℝ 2 (q' (φ₂ n)) z.1) H atTop :=
    tendstoUniformlyOn_univ.mp hhess
  refine ⟨ψ, hψ, g, hg, H, hH, ?_, ?_⟩
  · simpa [ψ, Function.comp_def] using hgrad'
  · simpa [q', ψ, Function.comp_def] using hhessUniform

/-- Uniform convergence of quotient gradients identifies the derivative of the pointwise limit.
The order-one multilinear jets are curried to Fréchet derivatives for `UniformLimitsDeriv`. -/
private theorem hasFDerivAt_limit_of_uniform_first_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V W : Set E} (hW : IsOpen W) (hWV : W ⊆ V)
    {q : ℕ → E → ℝ} {f : E → ℝ} {gV : V → (E [×1]→L[ℝ] ℝ)}
    (hq : ∀ n, ContDiffOn ℝ 2 (q n) W)
    (hpoint : ∀ x ∈ W, Tendsto (fun n ↦ q n x) atTop (𝓝 (f x)))
    (hgrad : TendstoUniformly
      (fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q n) z.1) gV atTop) :
    ∀ x (hx : x ∈ W), HasFDerivAt f
      (continuousMultilinearCurryFin1 ℝ E ℝ (gV ⟨x, hWV hx⟩)) x := by
  classical
  let c := continuousMultilinearCurryFin1 ℝ E ℝ
  let gE : E → E →L[ℝ] ℝ := fun x ↦
    if hx : x ∈ W then c (gV ⟨x, hWV hx⟩) else 0
  have hgE (x : E) (hx : x ∈ W) : gE x = c (gV ⟨x, hWV hx⟩) := by
    simp [gE, hx]
  have hgradCurry : TendstoUniformly
      (fun n (z : V) ↦ c (iteratedFDeriv ℝ 1 (q n) z.1))
      (fun z : V ↦ c (gV z)) atTop :=
    c.toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformly hgrad
  have hgradLocal : TendstoLocallyUniformlyOn
      (fun n x ↦ c (iteratedFDeriv ℝ 1 (q n) x)) gE atTop W :=
    tendstoLocallyUniformlyOn_of_uniformly_convergent_subtype
      hWV hgE hgradCurry
  have hderiv : ∀ n y, y ∈ W → HasFDerivAt (q n)
      (c (iteratedFDeriv ℝ 1 (q n) y)) y := by
    intro n y hy
    have hAt := (hq n y hy).contDiffAt (hW.mem_nhds hy)
    have hdiff := hAt.differentiableAt (by norm_num)
    have hhas := hdiff.hasFDerivAt
    have heq : fderiv ℝ (q n) y = c (iteratedFDeriv ℝ 1 (q n) y) := by
      ext v
      simp [c, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [heq] at hhas
    exact hhas
  intro x hx
  have hlimit := hasFDerivAt_of_tendstoLocallyUniformlyOn
    hW hgradLocal hderiv hpoint hx
  rw [hgE x hx] at hlimit
  exact hlimit

/-- From uniform-limit first-jet and Hessian identities, the pointwise limit is `C²` on the
smaller chart domain. The order-one multilinear jet is identified with the Fréchet derivative;
its derivative is continuous because it is the curry of the limiting Hessian. -/
private theorem local_limit_C2_of_two_uniform_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} (hW : IsOpen W)
    {f : E → ℝ} {g : E → (E [×1]→L[ℝ] ℝ)}
    {H : E → E →L[ℝ] (E [×1]→L[ℝ] ℝ)}
    (hfirst : ∀ x ∈ W, HasFDerivAt f
      (continuousMultilinearCurryFin1 ℝ E ℝ (g x)) x)
    (hsecond : ∀ x ∈ W, HasFDerivAt g (H x) x)
    (hH : ContinuousOn H W) :
    ContDiffOn ℝ 2 f W := by
  let c := continuousMultilinearCurryFin1 ℝ E ℝ
  let cL : (E [×1]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    c.toContinuousLinearEquiv.toContinuousLinearMap
  let d : E → E →L[ℝ] ℝ := fun x ↦ cL (g x)
  let d' : E → E →L[ℝ] (E →L[ℝ] ℝ) := fun x ↦ cL.comp (H x)
  have hD (x : E) (hx : x ∈ W) : HasFDerivAt d (d' x) x := by
    have hc : HasFDerivAt cL cL (g x) := cL.hasFDerivAt
    have h := hc.comp x (hsecond x hx)
    simpa [d, d', Function.comp_def] using h
  have hDcont : ContinuousOn d' W := by
    dsimp [d']
    fun_prop
  have hdifferentiable : DifferentiableOn ℝ d W := by
    intro x hx
    exact (hD x hx).differentiableAt.differentiableWithinAt
  have hfdderiv : Set.EqOn (fderiv ℝ d) d' W := by
    intro x hx
    exact (hD x hx).fderiv
  have hfdcont : ContinuousOn (fderiv ℝ d) W := by
    exact hDcont.congr hfdderiv
  have hd' : ContDiffOn ℝ 0 (fderiv ℝ d) W := contDiffOn_zero.mpr hfdcont
  have hdC1 : ContDiffOn ℝ 1 d W := by
    rw [show (1 : ℕ∞ω) = (0 : ℕ∞ω) + 1 by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen hW]
    exact ⟨hdifferentiable, by simp, hd'⟩
  have hfd : Set.EqOn (fderiv ℝ f) d W := by
    intro x hx
    have hh := (hfirst x hx).fderiv
    simpa [d, cL, c] using hh
  have hfdC1 : ContDiffOn ℝ 1 (fderiv ℝ f) W := by
    exact hdC1.congr hfd
  have hfdiff : DifferentiableOn ℝ f W := by
    intro x hx
    exact (hfirst x hx).differentiableAt.differentiableWithinAt
  rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen hW]
  exact ⟨hfdiff, by simp, hfdC1⟩

/-- Uniform convergence of quotient gradients and their curried Hessians identifies the limiting
gradient as differentiable. Smoothness of every quotient supplies the derivative hypotheses to
`hasFDerivAt_of_tendstoLocallyUniformlyOn`. -/
private theorem first_quotient_jet_hasFDerivAt_of_locally_uniform_hessian_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) (q : ℕ → E → ℝ)
    (hq : ∀ n, ContDiffOn ℝ 2 (q n) U)
    {g : E → (E [×1]→L[ℝ] ℝ)}
    (hjet : TendstoLocallyUniformlyOn
      (fun n x ↦ iteratedFDeriv ℝ 1 (q n) x) g Filter.atTop U)
    {H : E → E →L[ℝ] (E [×1]→L[ℝ] ℝ)}
    (hhess : TendstoLocallyUniformlyOn
      (fun n x ↦ continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin 2 ↦ E) ℝ (iteratedFDeriv ℝ 2 (q n) x)) H Filter.atTop U) :
    ∀ x ∈ U, HasFDerivAt g (H x) x := by
  intro x hx
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn hU hhess (by
    intro n y hy
    have hAt := (hq n y hy).contDiffAt (hU.mem_nhds hy)
    have hklt : (↑(1 : ℕ) : WithTop ℕ∞) < (↑(2 : ℕ) : WithTop ℕ∞) := by
      norm_num
    have hhas := hAt.differentiableAt_iteratedFDeriv hklt |>.hasFDerivAt
    have hfd := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ)
      (f := q n) (n := 1)) y
    rw [hfd] at hhas
    exact hhas)
    (fun y hy ↦ (hjet.tendsto_at hy)) hx

/-- The nonzero-quotient Schauder estimate and derivative-limit argument upgrade a `C²`
Monge–Ampère solution to `C³`. -/
private theorem contDiffOn_two_of_quotient_jet_limits
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U V W : Set E} (hU : IsOpen U) (hV : IsCompact V)
    (hVconvex : Convex ℝ V) (hVU : V ⊆ U) (hW : IsOpen W) (hWV : W ⊆ V)
    {α C : ℝ≥0} (hα : 0 < α) (q : ℕ → E → ℝ)
    (hq : ∀ n, ContDiffOn ℝ 2 (q n) U)
    (hqHolder : ∀ n, HolderBoundOn 2 α C V (q n))
    {f : E → ℝ} (hpoint : ∀ x ∈ W,
      Tendsto (fun n ↦ q n x) atTop (𝓝 (f x))) :
    ContDiffOn ℝ 2 f W := by
  classical
  obtain ⟨ψ, hψ, gV, hgV, HV, hHV, hgrad, hhess⟩ :=
    exists_subseq_tendstoUniformlyOn_quotient_first_and_second_jets
      hV hVconvex hU hVU hα hq hqHolder
  let q' : ℕ → E → ℝ := fun n ↦ q (ψ n)
  have hq' : ∀ n, ContDiffOn ℝ 2 (q' n) U := fun n ↦ hq (ψ n)
  let valueSeq : ℕ → C(V, ℝ) := fun n ↦ ⟨fun z ↦ q' n z.1, by
    apply continuousOn_iff_continuous_domRestrict.mp
    exact (hq' n).continuousOn.mono hVU⟩
  have hvalueLip (n : ℕ) : LipschitzOnWith C (q' n) V := by
    apply hVconvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      have hzU : z ∈ U := hVU hz
      exact ((hq' n z hzU).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by norm_num)
    · intro z hz
      have hbound := (hqHolder (ψ n)).1 1 (by norm_num) z hz
      have hboundReal : ‖iteratedFDeriv ℝ 1 (q' n) z‖ ≤ (C : ℝ) := by
        simpa [q'] using hbound
      have hderivBound : ‖fderiv ℝ (q' n) z‖ ≤ (C : ℝ) := by
        rw [← norm_iteratedFDeriv_one (q' n)]
        exact hboundReal
      exact_mod_cast hderivBound
  have hvalueLip' (n : ℕ) : LipschitzWith C (valueSeq n) := by
    change LipschitzWith C (V.domRestrict (q' n))
    exact lipschitzOnWith_iff_restrict.mp (hvalueLip n)
  have hvalueEquicontinuous :
      Equicontinuous (fun n ↦ (valueSeq n : V → ℝ)) :=
    (LipschitzWith.uniformEquicontinuous _ C hvalueLip').equicontinuous
  have hvalueBounded (z : V) : ∃ B : ℝ, ∀ n, ‖valueSeq n z‖ ≤ B := by
    refine ⟨C, ?_⟩
    intro n
    change ‖q' n (z : E)‖ ≤ (C : ℝ)
    have hb := (hqHolder (ψ n)).1 0 (by norm_num) (z : E) z.property
    simpa [q'] using hb
  let : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : LocallyCompactSpace V := by infer_instance
  have : SigmaCompactSpace V := by infer_instance
  obtain ⟨σ, valueLimit, hσ, hvalueConverges⟩ :=
    CalabiYau.CheegerGromovCompactness.arzelaAscoli_subseq_vec valueSeq
      hvalueEquicontinuous hvalueBounded
  have hvalueUniform : TendstoUniformly
      (fun n (z : V) ↦ valueSeq (σ n) z) valueLimit atTop := by
    exact tendstoUniformlyOn_univ.mp (hvalueConverges Set.univ isCompact_univ)
  let q'' : ℕ → E → ℝ := fun n ↦ q' (σ n)
  have hq'' : ∀ n, ContDiffOn ℝ 2 (q'' n) U := fun n ↦ hq' (σ n)
  have hpointBase (x : E) (hx : x ∈ W) :
      Tendsto (fun n ↦ q' n x) atTop (𝓝 (f x)) :=
    (hpoint x hx).comp hψ.tendsto_atTop
  have hgrad' : TendstoUniformly
      (fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q' n) z.1) gV atTop := by
    simpa [q'] using hgrad
  have hvalueLimit_eq (x : E) (hx : x ∈ W) :
      valueLimit ⟨x, hWV hx⟩ = f x := by
    have hpointTotal : Tendsto (fun n ↦ q'' n x) atTop (𝓝 (f x)) :=
      (hpoint x hx).comp (hψ.comp hσ).tendsto_atTop
    have hvalueAt := hvalueUniform.tendsto_at ⟨x, hWV hx⟩
    have hvalueAt' : Tendsto (fun n ↦ q'' n x) atTop
        (𝓝 (valueLimit ⟨x, hWV hx⟩)) := by
      convert hvalueAt using 1; rfl
    exact tendsto_nhds_unique hvalueAt' hpointTotal
  have hpoint' (x : E) (hx : x ∈ W) :
      Tendsto (fun n ↦ q'' n x) atTop (𝓝 (f x)) := by
    have hvalueAt := hvalueUniform.tendsto_at ⟨x, hWV hx⟩
    rw [hvalueLimit_eq x hx] at hvalueAt
    convert hvalueAt using 1; rfl
  have hgrad'' : TendstoUniformly
      (fun n (z : V) ↦ iteratedFDeriv ℝ 1 (q'' n) z.1) gV atTop := by
    simpa [q'', q', Function.comp_def] using
      tendstoUniformly_comp_strictMono hgrad' hσ
  let g : E → (E [×1]→L[ℝ] ℝ) :=
    fun x ↦ if hx : x ∈ W then gV ⟨x, hWV hx⟩ else 0
  have hg (x : E) (hx : x ∈ W) : g x = gV ⟨x, hWV hx⟩ := by
    simp [g, hx]
  have hgradLocal : TendstoLocallyUniformlyOn
      (fun n x ↦ iteratedFDeriv ℝ 1 (q'' n) x) g atTop W :=
    tendstoLocallyUniformlyOn_of_uniformly_convergent_subtype hWV hg hgrad''
  have hq''W : ∀ n, ContDiffOn ℝ 2 (q'' n) W :=
    fun n ↦ (hq'' n).mono (hWV.trans hVU)
  have hfirstV := hasFDerivAt_limit_of_uniform_first_jet hW hWV hq''W
    hpoint' hgrad''
  have hfirst : ∀ x ∈ W, HasFDerivAt f
      (continuousMultilinearCurryFin1 ℝ E ℝ (g x)) x := by
    intro x hx
    rw [hg x hx]
    exact hfirstV x hx
  let c₂ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 ↦ E) ℝ
  let H : E → E →L[ℝ] (E [×1]→L[ℝ] ℝ) :=
    fun x ↦ if hx : x ∈ W then c₂ (HV ⟨x, hWV hx⟩) else 0
  have hH (x : E) (hx : x ∈ W) : H x = c₂ (HV ⟨x, hWV hx⟩) := by
    simp [H, hx, c₂]
  have hhessUniform : TendstoUniformly
      (fun n (z : V) ↦ c₂ (iteratedFDeriv ℝ 2 (q' n) z.1))
      (fun z : V ↦ c₂ (HV z)) atTop := by
    have hmap := c₂.toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformly hhess
    simpa [q', Function.comp_def] using hmap
  have hhessUniform'' : TendstoUniformly
      (fun n (z : V) ↦ c₂ (iteratedFDeriv ℝ 2 (q'' n) z.1))
      (fun z : V ↦ c₂ (HV z)) atTop := by
    simpa [q'', q', Function.comp_def] using
      tendstoUniformly_comp_strictMono hhessUniform hσ
  have hhessLocal : TendstoLocallyUniformlyOn
      (fun n x ↦ c₂ (iteratedFDeriv ℝ 2 (q'' n) x)) H atTop W :=
    tendstoLocallyUniformlyOn_of_uniformly_convergent_subtype hWV hH hhessUniform''
  have hsecond := first_quotient_jet_hasFDerivAt_of_locally_uniform_hessian_limit
    hW q'' hq''W hgradLocal hhessLocal
  have hHcont : ContinuousOn H W := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : W.domRestrict H = fun z : W ↦ c₂ (HV ⟨z.1, hWV z.property⟩) := by
      funext z
      simp [H, c₂]
    rw [hEq]
    fun_prop
  exact local_limit_C2_of_two_uniform_jets hW hfirst hsecond hHcont

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem local_directional_derivative_contDiffOn_two
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hData : HasDifferenceQuotientSchauderData ω₀ G φ α)
    (i : cover.ι) (z₀ : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ interior (cover.piece i)) (v : EuclideanSpace ℂ (Fin n)) :
    ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ z₀ ∈ W ∧
      ContDiffOn ℝ 2
        (fun z ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z v) W := by
  classical
  rcases hData with ⟨hExact, hUniform⟩
  obtain ⟨r, δgeo, hr, hδgeo, hUopen, hUcompact, hUpiece, hVcompact, hVU,
    hsegments⟩ := exists_nested_chart_balls cover i z₀ v hz₀
  let U := Metric.ball z₀ (r / 2)
  let V := Metric.closedBall z₀ (r / 4)
  let W := Metric.ball z₀ (r / 8)
  have hU : IsOpen U := by simp [U]
  have hUcompact' : IsCompact (closure U) := by simpa [U] using hUcompact
  have hUpiece' : closure U ⊆ cover.piece i := by simpa [U] using hUpiece
  have hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
    hUpiece'.trans (cover.piece_in_target i)
  have hV : IsCompact V := by simpa [V] using hVcompact
  have hVU' : V ⊆ U := by simpa [U, V] using hVU
  have hW : IsOpen W := by simp [W]
  have hzW : z₀ ∈ W := by simp [W, hr]
  have hWV : W ⊆ V := by
    intro z hz
    change dist z z₀ < r / 8 at hz
    change dist z z₀ ≤ r / 4
    exact le_of_lt (lt_of_lt_of_le hz (by linarith [hr]))
  have hWtarget : W ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
    (hWV.trans hVU').trans (subset_closure.trans hUtarget)
  have hVconvex : Convex ℝ V := by
    simpa [V] using (convex_closedBall z₀ (r / 4))
  obtain ⟨δdata, lam, K, hδdata, hlam, hBounds⟩ :=
    hUniform (cover.base i) U hU hUcompact' hUtarget v
  let δgeoNN : ℝ≥0 := Real.toNNReal δgeo
  have hδgeoNN : (δgeoNN : ℝ) = δgeo := Real.coe_toNNReal δgeo hδgeo.le
  let δ : ℝ≥0 := min δgeoNN δdata
  have hδ : 0 < δ := lt_min (Real.toNNReal_pos.mpr hδgeo) hδdata
  have hsegments' : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U,
      segment ℝ z (z + h • v) ⊆ cover.piece i := by
    intro h hne hsmall z hz
    have hsmallGeo : |h| < δgeo := by
      calc
        |h| < (δ : ℝ) := hsmall
        _ ≤ δgeo := by rw [← hδgeoNN]; exact_mod_cast (min_le_left δgeoNN δdata)
    exact hsegments h hsmallGeo z hz
  have hStepBounds : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      (∀ z ∈ U, z + h • v ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target) →
      IsUniformlyEllipticOn (averagedChartInverse ω₀ φ (cover.base i) v h) lam U ∧
        (∀ j l, HolderBoundOn 0 α K U fun z ↦
          averagedChartInverse ω₀ φ (cover.base i) v h z j l) ∧
        HolderBoundOn 0 α K U (chartDifferenceQuotientRhs ω₀ G φ (cover.base i) v h) := by
    intro h hne hsmall htrans
    have hsmallData : |h| < (δdata : ℝ) := by
      calc
        |h| < (δ : ℝ) := hsmall
        _ ≤ δdata := by exact_mod_cast (min_le_right δgeoNN δdata)
    exact hBounds h hne hsmallData htrans
  obtain ⟨C, hC⟩ := local_differenceQuotient_schauder_bound hSch ω₀ α hα₀ hα₁
    hExact (cover.base i) U hU hUcompact' hUtarget V hVcompact
      (by simpa [U, V] using hVU) cover i rfl
    hφ hφGauge v δ lam K hsegments' hlam hStepBounds
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let f := φ ∘ e.symm
  let η : ℝ := min (δ : ℝ) (r / (8 * (1 + ‖v‖)))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by exact_mod_cast hδ) (by positivity)
  let hstep : ℕ → ℝ := fun k ↦ η / ((k : ℝ) + 2)
  have hstep_tendsto : Tendsto hstep atTop (𝓝 0) := by
    have hden : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    simpa [hstep] using (tendsto_const_nhds.div_atTop hden)
  have hstep_pos (k : ℕ) : 0 < hstep k := by
    dsimp [hstep]
    exact div_pos hη (by positivity)
  let hseq : ℕ → ℝ := fun k ↦ (-1 : ℝ) ^ k * hstep k
  have hseq_norm (k : ℕ) : ‖hseq k‖ = hstep k := by
    rw [norm_mul, Real.norm_eq_abs]
    simp [abs_of_pos (hstep_pos k)]
  have hseq_abs (k : ℕ) : |hseq k| = hstep k := by
    change |(-1 : ℝ) ^ k * hstep k| = hstep k
    rw [abs_mul, abs_pow]
    simp [abs_of_pos (hstep_pos k)]
  have hseq_norm_tendsto : Tendsto (fun k ↦ ‖hseq k‖) atTop (𝓝 0) := by
    convert hstep_tendsto using 1
    funext k
    exact hseq_norm k
  have hseq_tendsto : Tendsto hseq atTop (𝓝 0) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa using hseq_norm_tendsto
  have hseq_ne (k : ℕ) : hseq k ≠ 0 := by
    apply (norm_pos_iff.mp ?_)
    rw [hseq_norm]
    exact hstep_pos k
  have hstep_lt_eta (k : ℕ) : hstep k < η := by
    dsimp [hstep]
    have hk : 1 < (k : ℝ) + 2 := by
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [hη]
  have hηδ : η ≤ (δ : ℝ) := by dsimp [η]; exact min_le_left _ _
  have hseq_small (k : ℕ) : |hseq k| < (δ : ℝ) := by
    rw [hseq_abs]
    exact lt_of_lt_of_le (hstep_lt_eta k) hηδ
  have hseq_translate : ∀ k, ∀ z ∈ U, z + hseq k • v ∈ e.target := by
    intro k z hz
    have hseg := hsegments' (hseq k) (hseq_ne k) (hseq_small k) z hz
    exact cover.piece_in_target i (hseg (right_mem_segment ℝ z (z + hseq k • v)))
  let q : ℕ → EuclideanSpace ℂ (Fin n) → ℝ := fun k z ↦
    (f (z + hseq k • v) - f z) / hseq k
  have hq : ∀ k, ContDiffOn ℝ 2 (q k) U := by
    intro k
    obtain ⟨hqk, _⟩ := hC (hseq k) (hseq_ne k) (hseq_small k)
      (hseq_translate k)
    simpa [q, f, e] using hqk
  have hqHolder : ∀ k, HolderBoundOn 2 α C V (q k) := by
    intro k
    obtain ⟨_, hqk⟩ := hC (hseq k) (hseq_ne k) (hseq_small k)
      (hseq_translate k)
    simpa [q, f, e] using hqk
  have hchart : ContDiffOn ℝ 2 f e.target := by
    have h := (contMDiff_iff.mp hφ).2 (cover.base i) 0
    simpa [f, e, extChartAt, chartAt_self_eq] using h
  let L : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall z₀ (r / 4)
  have hLcompact : IsCompact L := by
    dsimp [L]
    exact isCompact_closedBall _ _
  have hLtarget : L ⊆ e.target := by
    intro z hz
    have hzV : z ∈ V := by simpa [L, V] using hz
    exact hUtarget (subset_closure (hVU' hzV))
  have hWL : W ⊆ L := by
    intro z hz
    have hzV : z ∈ V := hWV hz
    simpa [L, V] using hzV
  have hsegmentsValue : ∀ k z, z ∈ W →
      segment ℝ z (z + hseq k • v) ⊆ L := by
    intro k z hz
    have hzclosed : z ∈ Metric.closedBall z₀ (r / 8) := by
      rw [Metric.mem_closedBall]
      have hzball : dist z z₀ < r / 8 := by simpa [W] using Metric.mem_ball.mp hz
      exact le_of_lt hzball
    have hratio : ‖v‖ / (1 + ‖v‖) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [norm_nonneg v]
    have hηsmall : η ≤ r / (8 * (1 + ‖v‖)) := by
      dsimp [η]
      exact min_le_right _ _
    have hdisp : |hseq k| * ‖v‖ ≤ (r / 4) - (r / 8) := by
      calc
        |hseq k| * ‖v‖ = hstep k * ‖v‖ := by rw [hseq_abs]
        _ ≤ η * ‖v‖ := mul_le_mul_of_nonneg_right (le_of_lt (hstep_lt_eta k)) (norm_nonneg v)
        _ ≤ (r / (8 * (1 + ‖v‖))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hηsmall (norm_nonneg v)
        _ = (r / 8) * (‖v‖ / (1 + ‖v‖)) := by
          field_simp [ne_of_gt (by positivity : (0 : ℝ) < 8 * (1 + ‖v‖))]
        _ ≤ r / 8 := by exact mul_le_of_le_one_right (by positivity) hratio
        _ = (r / 4) - (r / 8) := by ring
    have hseg := signed_translation_segment_subset_compact_ball z₀ v
      (r := r / 8) (R := r / 4) (S := r / 2) (h := hseq k)
      (by linarith [hr]) (by linarith [hr]) hdisp hzclosed
    simpa [L] using hseg.1
  have hvalueUniform : TendstoUniformlyOn
      (fun k z ↦ (f (z + hseq k • v) - f z) / hseq k)
      (fun z ↦ fderiv ℝ f z v) atTop W :=
    signed_quotient_tendsto_uniformlyOn_fderiv
      (hU := isOpen_extChartAt_target (cover.base i)) hLcompact hLtarget hWL
      hchart v hseq hseq_tendsto (Filter.Eventually.of_forall hseq_ne) hsegmentsValue
  have hpoint : ∀ z ∈ W, Tendsto (fun k ↦ q k z) atTop
      (𝓝 (fderiv ℝ f z v)) := by
    intro z hz
    simpa [q] using hvalueUniform.tendsto_at hz
  refine ⟨W, hW, hzW, ?_⟩
  exact contDiffOn_two_of_quotient_jet_limits hU hV hVconvex hVU' hW hWV
    hα₀ q hq hqHolder (f := fun z ↦ fderiv ℝ f z v) hpoint

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
theorem solvesMongeAmpereC2_contMDiff_three_of_differenceQuotientSchauderData
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (hDifferenceQuotients : HasDifferenceQuotientSchauderData ω₀ G φ α) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 3 φ := by
  classical
  have := hG
  have := hEquation
  have hlocalChart (i : cover.ι) (z₀ : EuclideanSpace ℂ (Fin n))
      (hz₀ : z₀ ∈ interior (cover.piece i)) :
      ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ z₀ ∈ W ∧
        W ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
        ContDiffOn ℝ 3
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) W := by
    let E := EuclideanSpace ℂ (Fin n)
    let f : E → ℝ :=
      φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm
    let ι := Module.Basis.ofVectorSpaceIndex ℝ E
    let b : Module.Basis ι ℝ E := Module.Basis.ofVectorSpace ℝ E
    obtain ⟨WzeroRaw, hWzeroRawOpen, hzWzeroRaw, hWzeroRawDeriv⟩ :=
      local_directional_derivative_contDiffOn_two hSch ω₀ α hα₀ hα₁ hφ.1.1 cover
        hφGauge hDifferenceQuotients i z₀ hz₀ (0 : E)
    have hz₀target : z₀ ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
      cover.piece_in_target i (interior_subset hz₀)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_extChartAt_target (cover.base i)) z₀ hz₀target
    let Wzero := WzeroRaw ∩ Metric.ball z₀ r
    have hWzeroOpen : IsOpen Wzero := hWzeroRawOpen.inter Metric.isOpen_ball
    have hzWzero : z₀ ∈ Wzero := ⟨hzWzeroRaw, Metric.mem_ball_self hr⟩
    have hWzeroTarget : Wzero ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
      fun z hz ↦ hball hz.2
    have hWzeroDeriv : ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ f z (0 : E)) Wzero :=
      hWzeroRawDeriv.mono Set.inter_subset_left
    let Wj : ι → Set E := fun j ↦ Classical.choose
      (local_directional_derivative_contDiffOn_two hSch ω₀ α hα₀ hα₁ hφ.1.1 cover
        hφGauge hDifferenceQuotients i z₀ hz₀ (b j))
    have hWj (j : ι) : IsOpen (Wj j) ∧ z₀ ∈ Wj j ∧
        ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ f z (b j)) (Wj j) := by
      simpa [Wj, f, b] using Classical.choose_spec
        (local_directional_derivative_contDiffOn_two hSch ω₀ α hα₀ hα₁ hφ.1.1 cover
          hφGauge hDifferenceQuotients i z₀ hz₀ (b j))
    let W : Set E := Wzero ∩ ⋂ j : ι, Wj j
    have hWopen : IsOpen W := hWzeroOpen.inter (isOpen_iInter_of_finite fun j ↦ (hWj j).1)
    have hzW : z₀ ∈ W := ⟨hzWzero, Set.mem_iInter.mpr fun j ↦ (hWj j).2.1⟩
    have hWtarget : W ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
      fun z hz ↦ hWzeroTarget hz.1
    have hDcoord (j : ι) : ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ f z (b j)) W :=
      (hWj j).2.2.mono (fun z hz ↦ Set.mem_iInter.mp hz.2 j)
    let eLin : (E →L[ℝ] ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).symm.trans
        (b.constr ℝ).symm
    let e : (E →L[ℝ] ℝ) ≃L[ℝ] (ι → ℝ) := eLin.toContinuousLinearEquiv
    have heval (z : E) (j : ι) : e (fderiv ℝ f z) j = fderiv ℝ f z (b j) := by
      simp [e, eLin, LinearMap.toContinuousLinearMap, Module.Basis.constr_symm_apply]
    have hcoords : ContDiffOn ℝ 2 (fun z ↦ e (fderiv ℝ f z)) W := by
      apply contDiffOn_pi.2
      intro j
      exact (hDcoord j).congr fun z _ ↦ (heval z j).symm
    have hFderiv : ContDiffOn ℝ 2 (fderiv ℝ f) W := by
      have hcomp := e.symm.toContinuousLinearMap.contDiff.contDiffOn.comp hcoords
        (Set.mapsTo_univ _ _)
      simpa [e, Function.comp_def] using hcomp
    have hchart : ContDiffOn ℝ 2 f
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target := by
      have h := (contMDiff_iff.mp hφ.1.1).2 (cover.base i) 0
      simpa [f, extChartAt, chartAt_self_eq] using h
    have hfdiff : DifferentiableOn ℝ f W := by
      intro z hz
      have hzt : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
        hWtarget hz
      exact (((hchart z hzt).contDiffAt
        ((isOpen_extChartAt_target (cover.base i)).mem_nhds hzt)).differentiableAt
          (by norm_num)).differentiableWithinAt
    have hdirWithin (v : E) : ContDiffOn ℝ 2
        (fun z ↦ fderivWithin ℝ f W z v) W := by
      have hdir : ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ f z v) W :=
        hFderiv.clm_apply contDiffOn_const
      exact hdir.congr fun z hz ↦ by
        rw [fderivWithin_of_isOpen hWopen hz]
    have hchartThree : ContDiffOn ℝ 3 f W := by
      rw [show (3 : ℕ∞ω) = (2 : ℕ∞ω) + 1 by norm_num,
        contDiffOn_succ_iff_fderiv_of_isOpen hWopen]
      exact ⟨hfdiff, by simp, hFderiv⟩
    exact ⟨W, hWopen, hzW, hWtarget, hchartThree⟩
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 3 φ U := by
    obtain ⟨i, hximage⟩ := cover.interior_covers x
    obtain ⟨z₀, hz₀, hzx⟩ := hximage
    obtain ⟨W, hWopen, hzW, hWtarget, hchartThree⟩ := hlocalChart i z₀ hz₀
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
    let U : Set M := (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source ∩ e ⁻¹' W
    have hUopen : IsOpen U := isOpen_extChartAt_preimage (cover.base i) hWopen
    have hzTarget : z₀ ∈ e.target := cover.piece_in_target i (interior_subset hz₀)
    have hxSource : x ∈ e.source := by
      rw [← hzx]
      exact e.map_target hzTarget
    have hxU : x ∈ U := by
      constructor
      · rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base i)]
        exact hxSource
      · rw [← hzx]
        change e (e.symm z₀) ∈ W
        rw [e.right_inv hzTarget]
        exact hzW
    have hUsource : U ⊆ e.source := by
      intro y hy
      rw [extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base i)]
      exact hy.1
    have himage : e '' U = W := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy.2
      · intro hz
        refine ⟨e.symm z, ⟨?_, ?_⟩, e.right_inv (hWtarget hz)⟩
        · rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base i)]
          exact e.map_target (hWtarget hz)
        · change e (e.symm z) ∈ W
          rw [e.right_inv (hWtarget hz)]
          exact hz
    let et := extChartAt 𝓘(ℝ) (φ x)
    have htarget : ∀ y ∈ U, φ y ∈ et.source := by
      intro y hy
      simp [et, extChartAt, chartAt_self_eq]
    have hreg : ContDiffOn ℝ 3 (et ∘ φ ∘ e.symm) (e '' U) := by
      have hregW : ContDiffOn ℝ 3 (et ∘ φ ∘ e.symm) W := by
        have heq : et ∘ φ ∘ e.symm = φ ∘ e.symm := by
          funext z
          simp [et, extChartAt, chartAt_self_eq]
        rw [heq]
        simpa [e] using hchartThree
      simpa [himage] using hregW
    refine ⟨U, hUopen, hxU, ?_⟩
    rw [contMDiffOn_iff_of_subset_source' hUsource htarget]
    exact hreg
  apply contMDiff_of_locally_contMDiffOn
  exact hlocal

attribute [deprecated "unused hypotheses `hG` and `hEquation`; will be removed" (since := "2026-10-02")]
  KahlerForm.solvesMongeAmpereC2_contMDiff_three_of_differenceQuotientSchauderData

end KahlerForm
