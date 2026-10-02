module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.Chartwise.BufferedBalls

/-!
# Quantitative overlap transfer of the order-zero gauge

The chart-norm equivalence in Székelyhidi, §2.3, p. 31, at order zero. The constant is
chosen from the already fixed geometry, not from the function. In particular finiteness of
the gauge must not be used to choose an uncontrolled bound for the right-hand side.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

private theorem holderOnWith_zero_of_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ≥0} {s : Set E} {f : E → ℝ}
    (hf : HolderBoundOn 0 α C s f) : HolderOnWith C α f s := by
  have hseminorm : HolderOnWith C α (iteratedFDeriv ℝ 0 f) s := hf.2
  rw [iteratedFDeriv_zero_eq_comp] at hseminorm
  let c := continuousMultilinearCurryFin0 ℝ E ℝ
  intro x hx y hy
  have h := hseminorm x hx y hy
  change edist (c.symm (f x)) (c.symm (f y)) ≤
    (C : ℝ≥0∞) * edist x y ^ (α : ℝ) at h
  rw [c.symm.edist_map] at h
  exact h

/-- The exact `toNNReal` of the finite gauge controls the right-hand side on every buffered
ball with one geometry-only factor. The gauge hypothesis is indispensable: `toNNReal ⊤ = 0`.
A valid factor is `∑ p, max 1 (D.lipschitzConstant p ^ (α : ℝ))`. -/
theorem exists_bufferedBalls_rhs_gauge_factor
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (D : BufferedChartBalls cover i) (α : ℝ≥0) :
    ∃ B : ℝ≥0, ∀ q : M → ℝ,
      finiteChartHolderGauge cover 0 α q < ⊤ →
      ∀ p : D.ι, HolderBoundOn 0 α
        (B * (finiteChartHolderGauge cover 0 α q).toNNReal)
        (Metric.closedBall (D.center p) (2 * D.radius p))
        (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
  let B : ℝ≥0 := ∑ p : D.ι, max 1 (D.lipschitzConstant p ^ (α : ℝ))
  refine ⟨B, ?_⟩
  intro q hq p
  let G : ℝ≥0∞ := finiteChartHolderGauge cover 0 α q
  let C : ℝ≥0 := G.toNNReal
  let E := EuclideanSpace ℂ (Fin n)
  let e := extChartAt 𝓘(ℝ, E) (cover.base i)
  let ep := extChartAt 𝓘(ℝ, E) (cover.base (D.overlap p))
  let T : E → E := ep ∘ e.symm
  let u : E → ℝ := q ∘ ep.symm
  let g : E → ℝ := q ∘ e.symm
  have hfinite : G < ⊤ := hq
  have hcoe : (C : ℝ≥0∞) = G := ENNReal.coe_toNNReal (ne_of_lt hfinite)
  have hgauge : CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α
      (cover.piece (D.overlap p))
      (q ∘ (extChartAt 𝓘(ℝ, E) (cover.base (D.overlap p))).symm) ≤ (C : ℝ≥0∞) := by
    calc
      _ ≤ G := le_iSup _ (D.overlap p)
      _ = (C : ℝ≥0∞) := hcoe.symm
  have hchart : HolderBoundOn 0 α C (cover.piece (D.overlap p)) u := by
    exact ⟨(fun j hj z hz => CalabiYau.Schauder.spatialJet_norm_le hgauge hj hz),
      HolderWith.restrict_iff.mp
        (CalabiYau.Schauder.topSpatialJet_holderWith_restrict hgauge)⟩
  have hmaps : Set.MapsTo T (Metric.closedBall (D.center p) (2 * D.radius p))
      (cover.piece (D.overlap p)) := by
    intro z hz
    exact interior_subset (D.overlap_mapsTo p hz)
  have hL : LipschitzOnWith (D.lipschitzConstant p) T
      (Metric.closedBall (D.center p) (2 * D.radius p)) := by
    simpa [T, e, ep] using D.overlap_lipschitz p
  have hholder : HolderOnWith (C * (D.lipschitzConstant p ^ (α : ℝ))) α
      (u ∘ T) (Metric.closedBall (D.center p) (2 * D.radius p)) := by
    have h := (holderOnWith_zero_of_bound hchart).comp hL.holderOnWith hmaps
    simpa using h
  have hfun : ∀ z ∈ Metric.closedBall (D.center p) (2 * D.radius p),
      u (T z) = g z := by
    intro z hz
    dsimp [u, T, g, ep, e]
    exact congrArg q (D.overlap_inverse p z hz)
  have hholderg : HolderOnWith (C * (D.lipschitzConstant p ^ (α : ℝ))) α g
      (Metric.closedBall (D.center p) (2 * D.radius p)) := by
    intro z hz y hy
    have h := hholder z hz y hy
    simpa [hfun z hz, hfun y hy] using h
  have hvalue : ∀ z ∈ Metric.closedBall (D.center p) (2 * D.radius p),
      |g z| ≤ C * max 1 (D.lipschitzConstant p ^ (α : ℝ)) := by
    intro z hz
    have hv := hchart.1 0 le_rfl (T z) (hmaps hz)
    have hv' : |u (T z)| ≤ C := by
      simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hv
    have heq : u (T z) = g z := hfun z hz
    rw [← heq]
    exact le_trans hv' (le_mul_of_one_le_right (by positivity)
      (le_max_left 1 (D.lipschitzConstant p ^ (α : ℝ))))
  have hfactor : max 1 (D.lipschitzConstant p ^ (α : ℝ)) ≤ B := by
    change max 1 (D.lipschitzConstant p ^ (α : ℝ)) ≤
      ∑ x : D.ι, max 1 (D.lipschitzConstant x ^ (α : ℝ))
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun x : D.ι => max 1 (D.lipschitzConstant x ^ (α : ℝ)))
      (fun x hx => by positivity) (Finset.mem_univ p)
  have hconst : C * max 1 (D.lipschitzConstant p ^ (α : ℝ)) ≤ B * C := by
    calc
      _ ≤ C * B := mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = B * C := mul_comm _ _
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := by omega
    subst j
    have hv := hvalue z hz
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, g, e] using hv.trans hconst
  · have hholderDeriv : HolderOnWith (C * (D.lipschitzConstant p ^ (α : ℝ))) α
        (iteratedFDeriv ℝ 0 g) (Metric.closedBall (D.center p) (2 * D.radius p)) := by
      rw [iteratedFDeriv_zero_eq_comp]
      let c := continuousMultilinearCurryFin0 ℝ E ℝ
      intro z hz y hy
      change edist (c.symm (g z)) (c.symm (g y)) ≤ _
      rw [c.symm.edist_map]
      exact hholderg z hz y hy
    have hderivFinal : HolderOnWith (B * C) α
        (iteratedFDeriv ℝ 0 g) (Metric.closedBall (D.center p) (2 * D.radius p)) :=
      hholderDeriv.mono_const (by
        calc
          C * (D.lipschitzConstant p ^ (α : ℝ)) ≤
              C * max 1 (D.lipschitzConstant p ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
          _ ≤ B * C := hconst)
    simpa [g, e, C, G] using hderivFinal

end KahlerForm
