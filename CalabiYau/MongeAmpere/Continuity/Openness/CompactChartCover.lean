module

public import CalabiYau.Geometry.Complex.Holder

/-!
# Finite relatively compact chart cover

On a compact Hausdorff charted space, choose finitely many coordinate neighborhoods and shrink them
while still covering the space. Their closures give the fixed compact chart pieces used by the
Hölder norms in the continuity argument.
-/

@[expose] public section

open scoped Manifold ContDiff Topology

namespace KahlerForm

/-- A finite atlas by relatively compact chart pieces whose interiors cover the manifold. -/
structure CompactChartCover (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] where
  ι : Type
  [fintype_ι : Fintype ι]
  base : ι → M
  piece : ι → Set E
  isCompact_piece : ∀ i, IsCompact (piece i)
  piece_in_target : ∀ i, piece i ⊆ (extChartAt 𝓘(ℝ, E) (base i)).target
  interior_covers : ∀ x : M, ∃ i,
    x ∈ (extChartAt 𝓘(ℝ, E) (base i)).symm '' interior (piece i)

/-- A compact Hausdorff charted space has a finite cover by relatively compact chart pieces. -/
theorem exists_compactChartCover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] [CompactSpace M] :
    Nonempty (CompactChartCover E M) := by
  classical
  by_cases hM : IsEmpty M
  · let cover : CompactChartCover E M := {
      ι := Empty
      base := fun i => i.elim
      piece := fun i => i.elim
      isCompact_piece := fun i => i.elim
      piece_in_target := fun i => i.elim
      interior_covers := fun x => (hM.false x).elim
    }
    exact ⟨cover⟩
  · let hNonempty : Nonempty M := not_isEmpty_iff.mp hM
    letI := hNonempty
    let hLocallyCompact : LocallyCompactSpace M := inferInstance
    letI := hLocallyCompact
    let hFiniteDimensional : FiniteDimensional ℝ E :=
      FiniteDimensional.of_locallyCompact_manifold M (𝓘(ℝ, E))
    letI := hFiniteDimensional
    let e (x : M) := extChartAt 𝓘(ℝ, E) x
    let c (x : M) : E := e x x
    have hr (x : M) : ∃ r : ℝ, 0 < r ∧ Metric.ball (c x) r ⊆ (e x).target := by
      exact Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x)
        (c x) (mem_extChartAt_target (I := 𝓘(ℝ, E)) x)
    let r (x : M) : ℝ := Classical.choose (hr x)
    have hrpos (x : M) : 0 < r x := (Classical.choose_spec (hr x)).1
    have hrball (x : M) : Metric.ball (c x) (r x) ⊆ (e x).target :=
      (Classical.choose_spec (hr x)).2
    let piece (x : M) : Set E := Metric.closedBall (c x) (r x / 2)
    let V (x : M) : Set M := (chartAt E x).source ∩ (e x) ⁻¹' Metric.ball (c x) (r x / 2)
    have hVopen (x : M) : IsOpen (V x) := by
      exact isOpen_extChartAt_preimage (I := 𝓘(ℝ, E)) x Metric.isOpen_ball
    have hVcover : ∀ y : M, ∃ x : M, y ∈ V x := by
      intro y
      refine ⟨y, ?_⟩
      constructor
      · simpa [extChartAt_source] using mem_extChartAt_source (I := 𝓘(ℝ, E)) y
      · change e y y ∈ Metric.ball (c y) (r y / 2)
        rw [Metric.mem_ball]
        simp [c, dist_self, hrpos]
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hVopen (by
      intro y hy
      obtain ⟨x, hx⟩ := hVcover y
      exact Set.mem_iUnion.2 ⟨x, hx⟩)
    have hpieceCompact (x : M) : IsCompact (piece x) := isCompact_closedBall _ _
    have hpieceTarget (x : M) : piece x ⊆ (e x).target := by
      intro z hz
      apply hrball x
      rw [Metric.mem_ball]
      have hz' : dist (z : E) (c x) ≤ r x / 2 := by
        simpa [piece, Metric.mem_closedBall] using hz
      have hz'' : dist (c x) z ≤ r x / 2 := by simpa [dist_comm] using hz'
      linarith [hrpos x]
    have hpieceInterior (x : M) {z : E} (hz : z ∈ Metric.ball (c x) (r x / 2)) :
        z ∈ interior (piece x) := by
      exact Metric.ball_subset_interior_closedBall hz
    let ι := Fin s.card
    let base (i : ι) : M := (s.equivFin.symm i).1
    let cover : CompactChartCover E M := {
      ι := ι
      base := base
      piece := fun i => piece (base i)
      isCompact_piece := fun i => hpieceCompact (base i)
      piece_in_target := fun i => hpieceTarget (base i)
      interior_covers := by
        intro y
        obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
        let i : ι := s.equivFin ⟨x, hx⟩
        have hySource : y ∈ (e x).source := by
          have hs : (e x).source = (chartAt E x).source :=
            extChartAt_source (I := 𝓘(ℝ, E)) x
          rw [hs]
          exact hy.1
        have hyBall : e x y ∈ Metric.ball (c x) (r x / 2) := hy.2
        refine ⟨i, ⟨e x y, ?_, ?_⟩⟩
        · simpa [base, i] using hpieceInterior x hyBall
        · simpa [base, i, e] using (e x).left_inv hySource
    }
    exact ⟨cover⟩

end KahlerForm
