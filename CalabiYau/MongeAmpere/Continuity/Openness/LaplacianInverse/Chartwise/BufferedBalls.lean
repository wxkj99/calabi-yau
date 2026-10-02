module

public import CalabiYau.Geometry.Manifold.Holder.ChartNorm
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Buffered balls in a fixed chart

Székelyhidi, §2.3, pp. 31–32: shrink finitely many coordinate domains while retaining
coverage. The balls here are in the *output* chart. An overlap with a chart piece from the
fixed gauge cover supplies the right-hand-side norm. No regularity of the boundary of a
`CompactChartCover.piece` is assumed, and no thickening of a piece is used.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

/-- A geometry-only finite refinement of one compact chart piece. The closed ball of twice
the inner radius stays in the output chart and maps into the interior of a gauge-cover piece.
The transition and its inverse identity are asserted only on that buffered closed ball. -/
structure BufferedChartBalls
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι) where
  ι : Type
  [fintype_ι : Fintype ι]
  center : ι → EuclideanSpace ℂ (Fin n)
  radius : ι → ℝ
  radius_pos : ∀ p, 0 < radius p
  overlap : ι → cover.ι
  lipschitzConstant : ι → ℝ≥0
  outer_in_target : ∀ p, Metric.closedBall (center p) (2 * radius p) ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target
  overlap_mapsTo : ∀ p, Set.MapsTo
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (overlap p))) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
    (Metric.closedBall (center p) (2 * radius p)) (interior (cover.piece (overlap p)))
  overlap_lipschitz : ∀ p, LipschitzOnWith (lipschitzConstant p)
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (overlap p))) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
    (Metric.closedBall (center p) (2 * radius p))
  overlap_inverse : ∀ p, ∀ z ∈ Metric.closedBall (center p) (2 * radius p),
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (overlap p))).symm
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base (overlap p))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z
  inner_covers : cover.piece i ⊆ ⋃ p,
    interior (Metric.closedBall (center p) (radius p))

attribute [instance] BufferedChartBalls.fintype_ι

private theorem exists_local_bufferedBall
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ cover.piece i) :
    ∃ (j : cover.ι) (r : ℝ) (L : ℝ≥0), 0 < r ∧
      Metric.closedBall z (2 * r) ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
      Set.MapsTo
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
        (Metric.closedBall z (2 * r)) (interior (cover.piece j)) ∧
      LipschitzOnWith L
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
        (Metric.closedBall z (2 * r)) ∧
      (∀ y ∈ Metric.closedBall z (2 * r),
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm
          (((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)) ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) y) =
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm y) := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let e := extChartAt 𝓘(ℝ, E) (cover.base i)
  let x : M := e.symm z
  obtain ⟨j, w, hw, hxw⟩ := cover.interior_covers x
  let ep := extChartAt 𝓘(ℝ, E) (cover.base j)
  let T : E → E := ep ∘ e.symm
  let V : PartialEquiv E E := e.symm ≫ ep
  have hwtarget : w ∈ ep.target := cover.piece_in_target j (interior_subset hw)
  have hztarget : z ∈ e.target := cover.piece_in_target i hz
  have hxe : e.symm z = x := rfl
  have hTx : T z = w := by
    calc
      T z = ep (e.symm z) := rfl
      _ = ep (ep.symm w) := congrArg ep (by dsimp [x] at hxw; exact hxw.symm)
      _ = w := ep.right_inv hwtarget
  have hzV : z ∈ V.source := by
    change z ∈ (e.symm ≫ ep).source
    rw [PartialEquiv.trans_source]
    exact ⟨hztarget, by
      change e.symm z ∈ ep.source
      dsimp [x] at hxw
      rw [← hxw]
      exact ep.symm.map_source hwtarget⟩
  have hNtarget : e.target ∈ 𝓝 z :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (cover.base i)).mem_nhds hztarget
  have hNsource : V.source ∈ 𝓝 z := by
    change (e.target ∩ e.symm ⁻¹' ep.source) ∈ 𝓝 z
    have hNpre : e.symm ⁻¹' ep.source ∈ 𝓝 z :=
      (continuousAt_extChartAt_symm'' hztarget).preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓘(ℝ, E)) (cover.base j)).mem_nhds
          (by dsimp [x] at hxw; rw [← hxw]; exact ep.symm.map_source hwtarget))
    filter_upwards [hNtarget, hNpre] with y hy₁ hy₂
    exact ⟨hy₁, hy₂⟩
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hTdiff : ContDiffOn ℝ 1 T V.source := by
    have hC : ContDiffOn ℂ ⊤
        (extChartAt 𝓘(ℂ, E) (cover.base j) ∘
          (extChartAt 𝓘(ℂ, E) (cover.base i)).symm)
        (((extChartAt 𝓘(ℂ, E) (cover.base i)).symm ≫
          extChartAt 𝓘(ℂ, E) (cover.base j)).source) :=
      contDiffOn_ext_coord_change (I := 𝓘(ℂ, E))
        (cover.base j) (cover.base i)
    have hR := hC.restrict_scalars ℝ
    have hR1 := hR.of_le (show (1 : ℕ∞ω) ≤ ⊤ by exact le_top)
    simpa [T, V, e, ep, extChartAt, chartAt_self_eq] using hR1
  have hTcont : ContinuousAt T z :=
    hTdiff.continuousOn.continuousAt hNsource
  have hTxInterior : T z ∈ interior (cover.piece j) := by
    rw [hTx]
    exact hw
  have hNmap : T ⁻¹' interior (cover.piece j) ∈ 𝓝 z :=
    hTcont.preimage_mem_nhds ((isOpen_interior.mem_nhds hTxInterior))
  have hN : (e.target ∩ V.source ∩ T ⁻¹' interior (cover.piece j)) ∈ 𝓝 z := by
    filter_upwards [hNtarget, hNsource, hNmap] with y hy₁ hy₂ hy₃
    exact ⟨⟨hy₁, hy₂⟩, hy₃⟩
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hN
  let r : ℝ := δ / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hsmall (y : E) (hy : y ∈ Metric.closedBall z (2 * r)) : dist y z < δ := by
    have hy' : dist y z ≤ 2 * r := by
      simpa [Metric.mem_closedBall] using hy
    dsimp [r] at hy'
    linarith
  have hlocal (y : E) (hy : y ∈ Metric.closedBall z (2 * r)) :
      y ∈ e.target ∧ y ∈ V.source ∧ T y ∈ interior (cover.piece j) := by
    have hball : y ∈ Metric.ball z δ := by
      rw [Metric.mem_ball]
      exact hsmall y hy
    have hp := hδball hball
    rcases (show (y ∈ e.target ∧ y ∈ V.source) ∧
        T y ∈ interior (cover.piece j) by simpa only [Set.mem_inter_iff, Set.mem_preimage] using hp)
      with ⟨⟨htarget, hsource⟩, hmap⟩
    exact ⟨htarget, hsource, hmap⟩
  have hballSource (y : E) (hy : y ∈ Metric.closedBall z (2 * r)) :
      y ∈ V.source := (hlocal y hy).2.1
  have hballTarget (y : E) (hy : y ∈ Metric.closedBall z (2 * r)) : y ∈ e.target :=
    (hlocal y hy).1
  have hballMaps (y : E) (hy : y ∈ Metric.closedBall z (2 * r)) :
      T y ∈ interior (cover.piece j) := (hlocal y hy).2.2
  have hTclosed : ContDiffOn ℝ 1 T (Metric.closedBall z (2 * r)) := hTdiff.mono hballSource
  obtain ⟨L, hL⟩ := hTclosed.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall z (2 * r)) (isCompact_closedBall z (2 * r))
  refine ⟨j, r, L, hr, ?_, ?_, hL, ?_⟩
  · exact hballTarget
  · intro y hy
    exact hballMaps y hy
  · intro y hy
    have hyV := hballSource y hy
    have hyV' : e.symm y ∈ ep.source := hyV.2
    dsimp [T, ep, e]
    exact (extChartAt 𝓘(ℝ, E) (cover.base j)).left_inv hyV'

/-- Choose all buffers and overlap constants before a function or an exponent is supplied.
Compactness is needed only for `cover.piece i`; pieces may have irregular boundaries.
The fixed top regularity makes the standing `C¹` coordinate-transition assumption explicit;
merely continuous transitions do not supply `overlap_lipschitz`. -/
theorem exists_bufferedChartBalls
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι) :
    Nonempty (BufferedChartBalls cover i) := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let K := {z : E // z ∈ cover.piece i}
  have hloc (a : K) := exists_local_bufferedBall cover i a.property
  let j (a : K) := Classical.choose (hloc a)
  have hrEx (a : K) : ∃ r : ℝ, ∃ L : ℝ≥0, 0 < r ∧
      Metric.closedBall (a : E) (2 * r) ⊆
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target ∧
      Set.MapsTo
        ((extChartAt 𝓘(ℝ, E) (cover.base (j a))) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (Metric.closedBall (a : E) (2 * r)) (interior (cover.piece (j a))) ∧
      LipschitzOnWith L
        ((extChartAt 𝓘(ℝ, E) (cover.base (j a))) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (Metric.closedBall (a : E) (2 * r)) ∧
      (∀ y ∈ Metric.closedBall (a : E) (2 * r),
        (extChartAt 𝓘(ℝ, E) (cover.base (j a))).symm
          (((extChartAt 𝓘(ℝ, E) (cover.base (j a))) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) y) =
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm y) := by
    exact Classical.choose_spec (hloc a)
  let rad (a : K) := Classical.choose (hrEx a)
  have hLEx (a : K) : ∃ L : ℝ≥0, 0 < rad a ∧
      Metric.closedBall (a : E) (2 * rad a) ⊆
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target ∧
      Set.MapsTo
        ((extChartAt 𝓘(ℝ, E) (cover.base (j a))) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (Metric.closedBall (a : E) (2 * rad a)) (interior (cover.piece (j a))) ∧
      LipschitzOnWith L
        ((extChartAt 𝓘(ℝ, E) (cover.base (j a))) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (Metric.closedBall (a : E) (2 * rad a)) ∧
      (∀ y ∈ Metric.closedBall (a : E) (2 * rad a),
        (extChartAt 𝓘(ℝ, E) (cover.base (j a))).symm
          (((extChartAt 𝓘(ℝ, E) (cover.base (j a))) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) y) =
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm y) := by
    exact Classical.choose_spec (hrEx a)
  let lip (a : K) := Classical.choose (hLEx a)
  have hfields (a : K) := Classical.choose_spec (hLEx a)
  let U (a : K) : Set E := Metric.ball (a : E) (rad a)
  have hopen (a : K) : IsOpen (U a) := Metric.isOpen_ball
  have hcover : cover.piece i ⊆ ⋃ a : K, U a := by
    intro z hz
    refine Set.mem_iUnion.2 ⟨⟨z, hz⟩, ?_⟩
    change z ∈ Metric.ball z (rad ⟨z, hz⟩)
    rw [Metric.mem_ball, dist_self]
    exact (hfields ⟨z, hz⟩).1
  obtain ⟨s, hs⟩ := (cover.isCompact_piece i).elim_finite_subcover U hopen hcover
  let a (p : Fin s.card) : K := (s.equivFin.symm p).1
  let center (p : Fin s.card) : E := a p
  let radius (p : Fin s.card) : ℝ := rad (a p)
  let overlap (p : Fin s.card) : cover.ι := j (a p)
  let lipschitzConstant (p : Fin s.card) : ℝ≥0 := lip (a p)
  refine ⟨{
    ι := Fin s.card
    fintype_ι := inferInstance
    center := center
    radius := radius
    radius_pos := fun p => (hfields (a p)).1
    overlap := overlap
    lipschitzConstant := lipschitzConstant
    outer_in_target := ?_
    overlap_mapsTo := ?_
    overlap_lipschitz := ?_
    overlap_inverse := ?_
    inner_covers := ?_ }⟩
  · intro p
    exact (hfields (a p)).2.1
  · intro p
    exact (hfields (a p)).2.2.1
  · intro p
    exact (hfields (a p)).2.2.2.1
  · intro p y hy
    exact (hfields (a p)).2.2.2.2 y hy
  · intro z hz
    obtain ⟨b, hb, hbz⟩ := Set.mem_iUnion₂.mp (hs hz)
    let p : Fin s.card := s.equivFin ⟨b, hb⟩
    have hpa : a p = b := by simp [a, p]
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    have hbz' : z ∈ Metric.ball (center p) (radius p) := by
      simpa [U, center, radius, hpa] using hbz
    exact Metric.ball_subset_interior_closedBall hbz'

end KahlerForm
