module

public import CalabiYau.Geometry.Manifold.Holder.ChartNorm

/-!
# Finite buffered ball refinements

GT, Lemma 6.36, p. 136, is applied on balls, not on arbitrary compact chart pieces.
For every output piece we cover even its boundary by small balls in its chart target.
Each larger ball changes coordinates into a convex closed ball in the interior of a
possibly different gauge-cover piece. All this data is independent of functions.
-/

set_option autoImplicit false

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

/-- A finite geometry-only refinement of all original pieces. Three strictly nested radii
separate the set where convergence is used from the extraction set and the smoothness domain.
The donor ball is convex and lies inside a gauge piece, so lower-jet estimates can use line
segments there. `overlap_inverse` rules out using a chart outside its source. -/
structure FiniteChartBallRefinement {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) where
  ι : Type
  [fintype_ι : Fintype ι]
  chart : ι → cover.ι
  donor : ι → cover.ι
  center : ι → EuclideanSpace ℂ (Fin n)
  innerRadius : ι → ℝ
  middleRadius : ι → ℝ
  outerRadius : ι → ℝ
  inner_pos : ∀ p, 0 < innerRadius p
  inner_lt_middle : ∀ p, innerRadius p < middleRadius p
  middle_lt_outer : ∀ p, middleRadius p < outerRadius p
  outer_in_target : ∀ p, Metric.closedBall (center p) (outerRadius p) ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (chart p))).target
  donorCenter : ι → EuclideanSpace ℂ (Fin n)
  donorRadius : ι → ℝ
  donorRadius_pos : ∀ p, 0 < donorRadius p
  donor_in_interior : ∀ p, Metric.closedBall (donorCenter p) (donorRadius p) ⊆
    interior (cover.piece (donor p))
  overlap_mapsTo : ∀ p, Set.MapsTo
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (donor p))) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (chart p))).symm)
    (Metric.closedBall (center p) (outerRadius p))
    (Metric.closedBall (donorCenter p) (donorRadius p))
  overlap_inverse : ∀ p, ∀ z ∈ Metric.closedBall (center p) (outerRadius p),
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (donor p))).symm
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (donor p))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (chart p))).symm z)) =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (chart p))).symm z
  covers_piece : ∀ i : cover.ι, ∀ z ∈ cover.piece i, ∃ p : ι,
    chart p = i ∧ z ∈ Metric.ball (center p) (innerRadius p)

attribute [instance] FiniteChartBallRefinement.fintype_ι

private theorem finiteChartTransition_continuousAt {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    {i j : cover.ι} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target)
    (hp : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).source) :
    ContinuousAt (fun w => (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j))
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm w)) z := by
  let E := EuclideanSpace ℂ (Fin n)
  let ci := extChartAt 𝓘(ℝ, E) (cover.base i)
  let cj := extChartAt 𝓘(ℝ, E) (cover.base j)
  have hsymm : ContinuousAt ci.symm z := continuousAt_extChartAt_symm'' hz
  have hchart : ContinuousAt cj (ci.symm z) := continuousAt_extChartAt' hp
  change ContinuousAt (fun w => cj (ci.symm w)) z
  exact hchart.comp hsymm

private structure LocalChartBallData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (z : EuclideanSpace ℂ (Fin n)) where
  donor : cover.ι
  donorRadius : ℝ
  donorRadius_pos : 0 < donorRadius
  donorBall_interior : Metric.closedBall
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base donor))
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) donorRadius ⊆
      interior (cover.piece donor)
  outerRadius : ℝ
  outerRadius_pos : 0 < outerRadius
  outerBall_target : Metric.closedBall z outerRadius ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target
  overlap_mapsTo : Set.MapsTo
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base donor)) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
    (Metric.closedBall z outerRadius)
    (Metric.closedBall ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base donor))
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) donorRadius)
  overlap_source : ∀ w ∈ Metric.closedBall z outerRadius,
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm w ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base donor)).source

private theorem exists_localDonorBall {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (i : cover.ι) {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ cover.piece i) :
    ∃ j : cover.ι, ∃ d : ℝ, 0 < d ∧
      Metric.closedBall ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) d ⊆
          interior (cover.piece j) ∧
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
        Set.MapsTo
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)) ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
          (Metric.closedBall z r)
          (Metric.closedBall ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j))
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) d) ∧
        ∀ w ∈ Metric.closedBall z r,
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm w ∈
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).source := by
  let E := EuclideanSpace ℂ (Fin n)
  let ci := extChartAt 𝓘(ℝ, E) (cover.base i)
  let p := ci.symm z
  have hzTarget : z ∈ ci.target := cover.piece_in_target i hz
  obtain ⟨j, q, hq, hpq⟩ := cover.interior_covers p
  have hqPiece : q ∈ cover.piece j := interior_subset hq
  have hqTarget : q ∈ (extChartAt 𝓘(ℝ, E) (cover.base j)).target :=
    cover.piece_in_target j hqPiece
  have hcenter : (extChartAt 𝓘(ℝ, E) (cover.base j)) p = q := by
    rw [← hpq]
    exact (extChartAt 𝓘(ℝ, E) (cover.base j)).right_inv hqTarget
  obtain ⟨R, hR, hRball⟩ := Metric.isOpen_iff.mp
    (isOpen_interior : IsOpen (interior (cover.piece j))) q hq
  let d := R / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdonor : Metric.closedBall q d ⊆ interior (cover.piece j) := by
    exact (Metric.closedBall_subset_ball (by dsimp [d]; linarith)).trans hRball
  have hpSource : p ∈ (extChartAt 𝓘(ℝ, E) (cover.base j)).source := by
    rw [← hpq]
    exact (extChartAt 𝓘(ℝ, E) (cover.base j)).symm.map_source hqTarget
  have hsymmCont : ContinuousAt ci.symm z := continuousAt_extChartAt_symm'' hzTarget
  have hsourceN : (fun w : E => ci.symm w) ⁻¹'
      (extChartAt 𝓘(ℝ, E) (cover.base j)).source ∈ 𝓝 z :=
    hsymmCont.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ, E)) (cover.base j)).mem_nhds hpSource)
  have htrans := finiteChartTransition_continuousAt cover hzTarget hpSource
  have hqball : q ∈ Metric.ball q d := by
    simpa [Metric.mem_ball, dist_self] using hd
  have htransCenter : (extChartAt 𝓘(ℝ, E) (cover.base j)) p ∈ Metric.ball q d := by
    rw [hcenter]
    exact hqball
  have htransN : (fun w : E => (extChartAt 𝓘(ℝ, E) (cover.base j))
      ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm w)) ⁻¹' Metric.ball q d ∈ 𝓝 z :=
    htrans.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds htransCenter)
  have htargetN : ci.target ∈ 𝓝 z := (isOpen_extChartAt_target (I := 𝓘(ℝ, E))
    (cover.base i)).mem_nhds hzTarget
  have hN : (ci.target ∩
      (fun w : E => (extChartAt 𝓘(ℝ, E) (cover.base j)) (ci.symm w)) ⁻¹'
        Metric.ball q d) ∩ (fun w : E => ci.symm w) ⁻¹'
        (extChartAt 𝓘(ℝ, E) (cover.base j)).source ∈ 𝓝 z :=
    Filter.inter_mem (Filter.inter_mem htargetN htransN) hsourceN
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hN
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hclosed : Metric.closedBall z r ⊆ Metric.ball z r₀ := by
    exact Metric.closedBall_subset_ball (by dsimp [r]; linarith)
  refine ⟨j, d, hd, ?_, r, hr, ?_, ?_, ?_⟩
  · change Metric.closedBall ((extChartAt 𝓘(ℝ, E) (cover.base j)) p) d ⊆
      interior (cover.piece j)
    rw [hcenter]
    exact hdonor
  · intro w hw
    have hw' : w ∈ Metric.ball z r₀ := hclosed hw
    have hmem := hball hw'
    exact hmem.1.1
  · intro w hw
    have hw' : w ∈ Metric.ball z r₀ := hclosed hw
    have hmem := hball hw'
    have hval : (extChartAt 𝓘(ℝ, E) (cover.base j))
        ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm w) ∈ Metric.ball q d := by
      have hpre := hmem.1.2
      change w ∈ (fun w : E => (extChartAt 𝓘(ℝ, E) (cover.base j))
        ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm w)) ⁻¹' Metric.ball q d at hpre
      exact hpre
    change (extChartAt 𝓘(ℝ, E) (cover.base j))
      ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm w) ∈
        Metric.closedBall ((extChartAt 𝓘(ℝ, E) (cover.base j)) p) d
    rw [hcenter]
    exact Metric.ball_subset_closedBall hval
  · intro w hw
    have hw' : w ∈ Metric.ball z r₀ := hclosed hw
    exact hball hw' |>.2

private theorem exists_localChartBallData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (i : cover.ι) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ cover.piece i) :
    Nonempty (LocalChartBallData cover i z) := by
  obtain ⟨j, d, hd, hdonor, r, hr, htarget, hmaps, hsource⟩ :=
    exists_localDonorBall cover i hz
  exact ⟨{
    donor := j,
    donorRadius := d,
    donorRadius_pos := hd,
    donorBall_interior := hdonor,
    outerRadius := r,
    outerRadius_pos := hr,
    outerBall_target := htarget,
    overlap_mapsTo := hmaps,
    overlap_source := hsource }⟩

private theorem construct_finiteChartBallRefinement {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) :
    Nonempty (FiniteChartBallRefinement cover) := by
  classical
  let Local (i : cover.ι) (a : {z : EuclideanSpace ℂ (Fin n) // z ∈ cover.piece i}) :=
    Classical.choice (exists_localChartBallData cover i a.val a.property)
  let U (i : cover.ι) (a : {z : EuclideanSpace ℂ (Fin n) // z ∈ cover.piece i}) :
      Set (EuclideanSpace ℂ (Fin n)) :=
    Metric.ball a.val ((Local i a).outerRadius / 4)
  have hsubcover (i : cover.ι) : ∃ s : Finset
      {z : EuclideanSpace ℂ (Fin n) // z ∈ cover.piece i},
      ∀ z ∈ cover.piece i, ∃ a, a ∈ s ∧ z ∈ U i a := by
    obtain ⟨s, hs⟩ := (cover.isCompact_piece i).elim_finite_subcover
      (U i) (fun a => Metric.isOpen_ball) (by
        intro z hz
        refine Set.mem_iUnion.2 ⟨⟨z, hz⟩, ?_⟩
        change z ∈ Metric.ball z ((Local i ⟨z, hz⟩).outerRadius / 4)
        have hp := (Local i ⟨z, hz⟩).outerRadius_pos
        exact Metric.mem_ball_self (by positivity : 0 < (Local i ⟨z, hz⟩).outerRadius / 4))
    refine ⟨s, ?_⟩
    intro z hz
    obtain ⟨a, has, hza⟩ := Set.mem_iUnion₂.mp (hs hz)
    exact ⟨a, has, hza⟩
  let s (i : cover.ι) := Classical.choose (hsubcover i)
  have hs (i : cover.ι) := Classical.choose_spec (hsubcover i)
  let ι := Σ i : cover.ι, Fin (s i).card
  let selected (p : ι) : {z : EuclideanSpace ℂ (Fin n) // z ∈ cover.piece p.1} :=
    ((s p.1).equivFin.symm p.2).val
  let data (p : ι) := Local p.1 (selected p)
  let refinement : FiniteChartBallRefinement cover := {
    ι := ι
    chart := fun p => p.1
    donor := fun p => (data p).donor
    center := fun p => (selected p).val
    innerRadius := fun p => (data p).outerRadius / 4
    middleRadius := fun p => (data p).outerRadius / 2
    outerRadius := fun p => (data p).outerRadius
    inner_pos := by intro p; have hp := (data p).outerRadius_pos; positivity
    inner_lt_middle := by intro p; have hp := (data p).outerRadius_pos; nlinarith
    middle_lt_outer := by intro p; have hp := (data p).outerRadius_pos; nlinarith
    outer_in_target := by intro p; exact (data p).outerBall_target
    donorCenter := fun p =>
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base ((data p).donor)))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base p.1)).symm (selected p).val)
    donorRadius := fun p => (data p).donorRadius
    donorRadius_pos := by intro p; exact (data p).donorRadius_pos
    donor_in_interior := by intro p; exact (data p).donorBall_interior
    overlap_mapsTo := by intro p; exact (data p).overlap_mapsTo
    overlap_inverse := by
      intro p z hz
      exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base ((data p).donor))).left_inv ((data p).overlap_source z hz)
    covers_piece := by
      intro i z hz
      obtain ⟨a, ha, hzball⟩ := hs i z hz
      let k : Fin (s i).card := (s i).equivFin ⟨a, ha⟩
      let p : ι := ⟨i, k⟩
      have hselected : selected p = a := by simp [selected, p, k]
      refine ⟨p, rfl, ?_⟩
      have hzball' : z ∈ U i (selected p) := hselected ▸ hzball
      change z ∈ U i (selected p)
      exact hzball'
  }
  exact ⟨refinement⟩

/-- Finite subcovers of the original compact pieces, using the interior cover to choose
convex donor balls. No regularity or convexity of the original pieces is assumed. -/
theorem exists_finiteChartBallRefinement {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) :
    Nonempty (FiniteChartBallRefinement cover) := by
  exact construct_finiteChartBallRefinement cover

end KahlerForm
