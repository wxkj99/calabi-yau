module

public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative
import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ConnectedConstancy.EuclideanBallConstancy

/-!
# Local a.e. constancy on realified chart balls

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, §7.1:
zero distributional derivatives yield a.e. constancy on every interior Euclidean ball.
We transfer each ball separately via the positive smooth Kähler volume density; a chart
*target* may be disconnected, so it cannot be assigned a single constant at this stage.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology

namespace KahlerForm

private theorem chart_ball_data
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M]
    (ω₀ : KahlerForm n M) (u : M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (hweak : HasZeroWeakDerivativeInCharts (n := n) (M := M) u)
    (a : M) (_hn : n ≠ 0) :
    let d := Module.finrank ℝ (EuclideanSpace ℂ (Fin n))
    let q : EuclideanSpace ℝ (Fin d) :=
      toEuclidean (E := EuclideanSpace ℂ (Fin n))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a) a)
    let U : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
      u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall q r ⊆ Sobolev.Chart.chartTargetEuclid
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a ∧
      MemLp U (ENNReal.ofReal 2) (MeasureTheory.volume.restrict (Metric.ball q r)) ∧
      ∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball q r →
        ∫ y in Metric.ball q r,
          U y * (fderiv ℝ φ y) (EuclideanSpace.single i 1) = 0 := by
  dsimp
  let d := Module.finrank ℝ (EuclideanSpace ℂ (Fin n))
  let q : EuclideanSpace ℝ (Fin d) :=
    toEuclidean (E := EuclideanSpace ℂ (Fin n))
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a) a)
  let U : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
    u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
  let Ω := Sobolev.Chart.chartTargetEuclid
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a
  have hΩ : IsOpen Ω := by
    simpa [Ω] using Sobolev.Chart.chartTargetEuclid_isOpen
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a
  have hq : q ∈ Ω := by
    simp [q, Ω, Sobolev.Chart.chartTargetEuclid]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ q hq
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hclosed : Metric.closedBall q r ⊆ Ω := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    dsimp [r] at hy ⊢
    linarith
  have hKcompact : IsCompact (Metric.closedBall q r) := isCompact_closedBall q r
  have hUclosed : MemLp U (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.closedBall q r)) := by
    simpa [U] using chartLocal_memLp_of_global_memLp ω₀ u hu a
      (Metric.closedBall q r) hKcompact hclosed
  have hUball : MemLp U (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball q r)) := by
    have hμ : (MeasureTheory.volume.restrict (Metric.closedBall q r)).restrict
        (Metric.ball q r) = MeasureTheory.volume.restrict (Metric.ball q r) := by
      rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet]
      congr 1
      exact Set.inter_eq_left.mpr Metric.ball_subset_closedBall
    rw [← hμ]
    exact hUclosed.restrict (Metric.ball q r)
  refine ⟨r, hr, hclosed, hUball, ?_⟩
  intro i φ hφ hφcompact hφsupport
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
    U y * (fderiv ℝ φ y) (EuclideanSpace.single i 1)
  have hzeroOutside : ∀ y, y ∉ Metric.ball q r → g y = 0 := by
    intro y hy
    have hy' : y ∉ tsupport φ := fun hs => hy (hφsupport hs)
    have hd : fderiv ℝ φ y = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := φ) (x := y) hy'
    simp [g, hd]
  have hglobalBall := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))))
    (s := Metric.ball q r) (f := g) hzeroOutside
  have hglobalΩ := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))))
    (s := Ω) (f := g) (by
      intro y hy
      have hyball : y ∉ Metric.ball q r := fun hb =>
        hy (hclosed (Metric.ball_subset_closedBall hb))
      exact hzeroOutside y hyball)
  have hclosed' : Metric.closedBall
      (toEuclidean (E := EuclideanSpace ℂ (Fin n))
        ((chartAt (EuclideanSpace ℂ (Fin n)) a) a)) r ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a := by
    simpa [q, Ω, Sobolev.Chart.chartTargetEuclid, extChartAt] using hclosed
  have hweak' : (∫ y in Ω, g y) = 0 := by
    simpa [g, U, Ω] using hweak a i φ hφ hφcompact
      (hφsupport.trans (Metric.ball_subset_closedBall.trans hclosed'))
  calc
    ∫ y in Metric.ball q r, g y = ∫ y, g y := hglobalBall
    _ = ∫ y in Ω, g y := hglobalΩ.symm
    _ = 0 := hweak'

/-- Transfer a.e. equality on an interior real chart ball to an open manifold neighborhood.
The positive smooth chart density makes Euclidean and Kähler null sets equivalent there. -/
private theorem chart_ball_ae_to_manifold_neighborhood
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (u : M → ℝ) (a : M)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))
    (hq : q = toEuclidean (E := EuclideanSpace ℂ (Fin n))
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a) a))
    (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall q r ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (c : ℝ)
    (hae : ∀ᵐ y ∂(MeasureTheory.volume.restrict (Metric.ball q r)),
      u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) = c) :
    ∃ V : Set M, IsOpen V ∧ a ∈ V ∧
      ∀ᵐ y ∂(ω₀.volume.restrict V), u y = c := by
  let C := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let e := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  let R := EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))
  let K := chartAt (EuclideanSpace ℂ (Fin n)) a
  let B : Set (EuclideanSpace ℂ (Fin n)) := e.symm '' Metric.ball q r
  let V : Set M := K.symm '' B
  have hBopen : IsOpen B := by
    change IsOpen (e.symm '' Metric.ball q r)
    exact e.symm.isOpenMap (Metric.ball q r) Metric.isOpen_ball
  have hBtarget : B ⊆ K.target := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hy' : y ∈ Metric.closedBall q r := Metric.ball_subset_closedBall hy
    have hyt : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a := hball hy'
    change y ∈ e '' C.target at hyt
    rcases hyt with ⟨z, hzt, heq⟩
    have hsymm : e.symm y = z := by rw [← heq]; exact e.symm_apply_apply z
    have hzt' : z ∈ K.target := by
      simpa [C, K, extChartAt_target] using hzt
    rw [hsymm]
    exact hzt'
  have hVopen : IsOpen V := by
    exact K.symm.isOpen_image_of_subset_source hBopen hBtarget
  have hca : K a ∈ K.target := K.map_source (mem_chart_source _ a)
  have hqball : q ∈ Metric.ball q r := Metric.mem_ball_self hr
  have hq' : q = e (K a) := by
    simpa [C, K, extChartAt_coe] using hq
  have hV : a ∈ V := by
    refine ⟨e.symm q, ⟨q, hqball, rfl⟩, ?_⟩
    rw [hq', e.symm_apply_apply]
    exact K.left_inv (mem_chart_source _ a)
  let N : Set R := {y | u (C.symm (e.symm y)) ≠ c}
  have hN : (MeasureTheory.volume.restrict (Metric.ball q r)) N = 0 := by
    exact (MeasureTheory.ae_iff.mp hae)
  obtain ⟨N', hNN', hN'meas, hN'zero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hN
  let N'' := N' ∩ Metric.ball q r
  have hN''meas : MeasurableSet N'' := hN'meas.inter Metric.isOpen_ball.measurableSet
  have hN''subset : N'' ⊆ Metric.ball q r := Set.inter_subset_right
  have hN''res : (MeasureTheory.volume.restrict (Metric.ball q r)) N'' = 0 :=
    measure_mono_null (Set.inter_subset_left : N'' ⊆ N') hN'zero
  have hN''zero : (MeasureTheory.volume : Measure R) N'' = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hN''meas] at hN''res
    simpa [N'', Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hN''res
  have hNnull : (MeasureTheory.volume : Measure R) N'' = 0 := hN''zero
  let D : Set (EuclideanSpace ℂ (Fin n)) := e.symm '' N''
  have hDmeas : MeasurableSet D := by
    exact e.symm.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hN''meas
  have hmap : Measure.map (e.symm : R → EuclideanSpace ℂ (Fin n))
      (MeasureTheory.volume : Measure R) =
      (Classical.choose (LinearMap.exists_map_addHaar_eq_smul_addHaar
        (e.symm.toLinearMap) (MeasureTheory.volume : Measure R)
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) e.symm.surjective)) •
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    exact (Classical.choose_spec (LinearMap.exists_map_addHaar_eq_smul_addHaar
      (e.symm.toLinearMap) (MeasureTheory.volume : Measure R)
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) e.symm.surjective)).2
  have hDzero : (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) D = 0 := by
    have h : Measure.map (e.symm : R → EuclideanSpace ℂ (Fin n))
        (MeasureTheory.volume : Measure R) D =
        (MeasureTheory.volume : Measure R) (e.symm ⁻¹' D) :=
      MeasureTheory.Measure.map_apply e.symm.continuous.measurable hDmeas
    rw [hmap] at h
    simp only [MeasureTheory.Measure.smul_apply] at h
    have hpre : e.symm ⁻¹' D = N'' := Set.preimage_image_eq _ e.symm.injective
    rw [hpre, hNnull] at h
    have hcpos := (Classical.choose_spec (LinearMap.exists_map_addHaar_eq_smul_addHaar
      (e.symm.toLinearMap) (MeasureTheory.volume : Measure R)
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) e.symm.surjective)).1
    exact (mul_eq_zero.mp h).resolve_left (by positivity)
  have hDtarget : D ⊆ K.target := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hBtarget ⟨y, hN''subset hy, rfl⟩
  have hDsubsetB : D ⊆ B := Set.image_mono hN''subset
  have hCeqK : ∀ z, C.symm z = K.symm z := by
    intro z
    simp [C, K]
  let T : K.target ≃ₜ K.source := K.toHomeomorphSourceTarget.symm
  let Dsub : Set K.target := {z | (z : EuclideanSpace ℂ (Fin n)) ∈ D}
  have hDsubmeas : MeasurableSet Dsub := hDmeas.preimage measurable_subtype_coe
  let Wsub : Set K.source := T '' Dsub
  have hWsubmeas : MeasurableSet Wsub :=
    T.measurableEmbedding.measurableSet_image.mpr hDsubmeas
  let W : Set M := (Subtype.val : K.source → M) '' Wsub
  have hWmeas : MeasurableSet W :=
    (MeasurableEmbedding.subtype_coe K.open_source.measurableSet).measurableSet_image.mpr
      hWsubmeas
  have hTapply (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K.target) :
      ((T ⟨z, hz⟩ : K.source) : M) = K.symm z := by
    rfl
  have hWchart : W = K.symm '' D := by
    ext x
    constructor
    · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      rcases t with ⟨z, hzt⟩
      refine ⟨z, ht, ?_⟩
      exact (hTapply z hzt).symm
    · rintro ⟨z, hz, rfl⟩
      have hzt := hDtarget hz
      refine ⟨⟨K.symm z, K.symm.map_source hzt⟩, ?_, rfl⟩
      refine ⟨⟨z, hzt⟩, hz, ?_⟩
      apply Subtype.ext
      exact hTapply z hzt
  have hWsubsetV : W ⊆ V := by
    rw [hWchart]
    exact Set.image_mono hDsubsetB
  have hWsource : W ⊆ K.source := by
    rw [hWchart]
    rintro x ⟨z, hz, rfl⟩
    exact K.symm.map_source (hDtarget hz)
  have hWpartial : W = C.symm '' D := by
    rw [hWchart]
    exact Set.image_congr fun z hz => (hCeqK z).symm
  have hCtarget : D ⊆ C.target := by
    simpa [C, K, extChartAt_target] using hDtarget
  have hCimage : C '' W = D := by
    rw [hWpartial]
    ext z
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, hcx⟩
      rw [C.right_inv (hCtarget hw)] at hcx
      rw [← hcx]
      exact hw
    · intro hz
      exact ⟨C.symm z, ⟨z, hz, rfl⟩, C.right_inv (hCtarget hz)⟩
  have hWnull : ω₀.volume W = 0 := by
    rw [ω₀.volume_apply_of_subset_source a hWmeas (by
      simpa [K] using hWsource), hCimage]
    exact MeasureTheory.setLIntegral_measure_zero D _ hDzero
  have hbadSubset : {x : M | u x ≠ c} ∩ V ⊆ W := by
    rintro x ⟨hbad, hxV⟩
    rcases hxV with ⟨z, ⟨y, hyball, rfl⟩, rfl⟩
    have hbad' : u (C.symm (e.symm y)) ≠ c := by
      rw [← hCeqK (e.symm y)] at hbad
      exact hbad
    have hyN : y ∈ N := by
      change u (C.symm (e.symm y)) ≠ c
      exact hbad'
    have hyN' : y ∈ N' := hNN' hyN
    have hyN'' : y ∈ N'' := ⟨hyN', hyball⟩
    rw [hWchart]
    exact ⟨e.symm y, ⟨y, hyN'', rfl⟩, rfl⟩
  have hbadVzero : (ω₀.volume.restrict V) {x | u x ≠ c} = 0 := by
    rw [Measure.restrict_apply_eq_zero' hVopen.measurableSet]
    exact measure_mono_null hbadSubset hWnull
  refine ⟨V, hVopen, hV, ?_⟩
  exact MeasureTheory.ae_iff.mpr hbadVzero

/-- In complex dimension zero the coordinate chart model is one point. Every sufficiently
small chart-source neighborhood is a singleton; no derivative index exists or is needed. -/
private theorem chart_ball_zero_dimensional
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 0)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 0)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm 0 M) (u : M → ℝ) (a : M) :
    ∃ V : Set M, IsOpen V ∧ a ∈ V ∧
      ∃ c : ℝ, ∀ᵐ y ∂(ω₀.volume.restrict V), u y = c := by
  let V := (chartAt (EuclideanSpace ℂ (Fin 0)) a).source
  have hVopen : IsOpen V := by
    simpa [V] using (chartAt (EuclideanSpace ℂ (Fin 0)) a).open_source
  have haV : a ∈ V := by
    simpa [V] using mem_chart_source (EuclideanSpace ℂ (Fin 0)) a
  have : Subsingleton (EuclideanSpace ℂ (Fin 0)) := inferInstance
  have hconst : ∀ y ∈ V, y = a := by
    intro y hy
    have hchart : (chartAt (EuclideanSpace ℂ (Fin 0)) a) y =
        (chartAt (EuclideanSpace ℂ (Fin 0)) a) a := Subsingleton.elim _ _
    calc
      y = (chartAt (EuclideanSpace ℂ (Fin 0)) a).symm
          ((chartAt (EuclideanSpace ℂ (Fin 0)) a) y) := by
            symm
            exact (chartAt (EuclideanSpace ℂ (Fin 0)) a).left_inv (by simpa [V] using hy)
      _ = (chartAt (EuclideanSpace ℂ (Fin 0)) a).symm
          ((chartAt (EuclideanSpace ℂ (Fin 0)) a) a) := congrArg _ hchart
      _ = a := (chartAt (EuclideanSpace ℂ (Fin 0)) a).left_inv haV
  refine ⟨V, hVopen, haV, u a, ?_⟩
  filter_upwards [ae_restrict_mem hVopen.measurableSet] with y hy
  rw [hconst y hy]

/-- Chartwise vanishing weak derivatives give a.e. constancy *locally around each point*.
This formulation remains valid when the chart image is disconnected. -/
theorem chartBall_ae_eq_const_of_zero_weak_derivative_in_charts
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M]
    (ω₀ : KahlerForm n M) (u : M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (hweak : HasZeroWeakDerivativeInCharts (n := n) (M := M) u)
    (a : M) :
    ∃ V : Set M, IsOpen V ∧ a ∈ V ∧
      ∃ c : ℝ, ∀ᵐ y ∂(ω₀.volume.restrict V), u y = c := by
  by_cases hn : n = 0
  · subst n
    exact chart_ball_zero_dimensional ω₀ u a
  · let d := Module.finrank ℝ (EuclideanSpace ℂ (Fin n))
    let q : EuclideanSpace ℝ (Fin d) :=
      toEuclidean (E := EuclideanSpace ℂ (Fin n))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a) a)
    let U : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
      u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
    have : NeZero d := by
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hdim : d = 2 * n := by
        simp [d, finrank_real_of_complex]
      exact ⟨by rw [hdim]; omega⟩
    obtain ⟨r, hr, hball, hL2, hzero⟩ := chart_ball_data ω₀ u hu hweak a hn
    obtain ⟨c, hc⟩ := euclideanBall_ae_eq_const_of_zero_weak_derivative
      U q r hr hL2 hzero
    obtain ⟨V, hVopen, haV, hae⟩ :=
      chart_ball_ae_to_manifold_neighborhood ω₀ u a q rfl r hr hball c hc
    exact ⟨V, hVopen, haV, c, hae⟩

end KahlerForm
