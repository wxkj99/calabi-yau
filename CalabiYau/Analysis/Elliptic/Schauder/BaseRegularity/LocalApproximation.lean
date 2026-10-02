module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CoefficientBounds
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.SolutionJets
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.SourceBound
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall

/-! # Fixed-radius local approximation for base Schauder regularity

The canonical coefficient and solution rows share one normalized kernel on a compact collar.
This is a local replacement for, not a construction of, globally bounded rows on arbitrary open
sets. The source estimate includes the coefficient--Hessian covariance; uniform convergence
alone would not imply convergence of its Hölder bound.
-/

@[expose] public section

open Set Filter Matrix
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

/-- Construct the local data on a closed ball strictly contained in an open source set. -/
theorem exists_localSchauderApproximationData {n : ℕ}
    {α lam K K₀ K₁ : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {R S : ℝ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hU : IsOpen U) (hR : 0 < R) (hRS : R < S)
    (hSU : Metric.closedBall c S ⊆ U)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ 2 u U) (hEll : IsUniformlyEllipticOn A lam U)
    (hAH : ∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l)
    (hL₀ : ContDiffOn ℝ 0 (complexEllipticOp A u) U)
    (hLH : HolderBoundOn 0 α K₁ U (complexEllipticOp A u))
    (hBound : ∀ z ∈ U, |u z| ≤ K₀) :
    LocalSchauderApproximationData α lam K K₀ K₁ c R S A u := by
  obtain ⟨η, hη, hCollar⟩ :=
    (isCompact_closedBall c S).exists_thickening_subset_open hU hSU
  have hS : 0 < S := by linarith
  obtain ⟨hAsmooth, hEllSeq, hAconv⟩ := localFixedCoefficientSeq_regular
    hU hR hRS hη hCollar hA₀ hEll
  obtain ⟨husmooth, hValue, hJets⟩ := localFixedMollify_solutionJets
    hU hR hRS hη hCollar hu hBound
  obtain ⟨ε, hε, hSource⟩ := localFixedMollify_sourceBound hα₀ hα₁ hU
    hS hη hCollar hA₀ hu hAH hL₀ hLH
  have hAHSeq : ∀ m j l, HolderBoundOn 0 α (K + 1) (Metric.ball c S)
      (fun z ↦ localFixedCoefficientSeq U hη A m z j l) := by
    intro m j l
    exact (localFixedMollify_holderBoundOn_zero hU hS hη hCollar
      (hA₀ j l).continuousOn (hAH j l) m).mono_const (by simp)
  refine ⟨ε, localFixedCoefficientSeq U hη A, (fun m ↦ localFixedMollify U hη m u),
    hε, hAsmooth, husmooth, hEllSeq, hAHSeq, hSource, ?_, hAconv, hJets⟩
  intro m z hz
  exact (hValue m z hz).trans (by exact_mod_cast (le_add_of_nonneg_right (ε m).coe_nonneg))

/-- The order-two Hölder bound passes through local convergence of the first three jets. -/
theorem holderBoundOn_two_of_localJetLimit {n : ℕ}
    {α B : ℝ≥0} {Bseq : ℕ → ℝ≥0}
    {s : Set (EuclideanSpace ℂ (Fin n))}
    {useq : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hB : Tendsto Bseq atTop (𝓝 B))
    (hEst : ∀ m, HolderBoundOn 2 α (Bseq m) s (useq m))
    (hD : ∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m z ↦ iteratedFDeriv ℝ j (useq m) z)
      (iteratedFDeriv ℝ j u) atTop s) :
    HolderBoundOn 2 α B s u := by
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hnorm := ((hD j hj).tendsto_at hz).norm
    have hBReal : Tendsto (fun m ↦ (Bseq m : ℝ)) atTop (𝓝 (B : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hB
    apply le_of_tendsto_of_tendsto hnorm hBReal
    exact Eventually.of_forall fun m ↦ (hEst m).1 j hj z hz
  · intro x hx y hy
    have hleft := ((hD 2 le_rfl).tendsto_at hx).edist
      ((hD 2 le_rfl).tendsto_at hy)
    have hcoe : Continuous (fun b : ℝ≥0 ↦ (b : ENNReal)) := by fun_prop
    have hcoef := hcoe.continuousAt.tendsto.comp hB
    have hright : Tendsto
        (fun m ↦ (Bseq m : ENNReal) * edist x y ^ (α : ℝ)) atTop
        (𝓝 ((B : ENNReal) * edist x y ^ (α : ℝ))) :=
      ENNReal.Tendsto.mul_const hcoef
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg α.coe_nonneg (edist_ne_top x y)))
    apply le_of_tendsto_of_tendsto hleft hright
    exact Eventually.of_forall fun m ↦ (hEst m).2 x hx y hy

/-- The local smooth estimate passes to the original solution. Its constant is chosen before
`c`, `A`, `u`, `K₀`, and `K₁`; the approximating error sequence need not be uniformly at most one. -/
theorem localSchauderApproximationEstimate {n : ℕ} (hn : 0 < n)
    (α lam K : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1) (hLam : 0 < lam)
    (R S : ℝ) (hR : 0 < R) (hRS : R < S) :
    ∃ C : ℝ≥0, ∀ (c : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u : EuclideanSpace ℂ (Fin n) → ℝ) (K₀ K₁ : ℝ≥0),
      LocalSchauderApproximationData α lam K K₀ K₁ c R S A u →
      HolderBoundOn 2 α (C * (K₁ + K₀)) (Metric.closedBall c (R / 2)) u := by
  obtain ⟨C, hSmooth⟩ := smoothComplexBallInteriorEstimate hn
    α (lam / 2) (K + 1) hα₀ hα₁ (by positivity)
    (R / 2) ((R + S) / 2) (by positivity) (by linarith)
  refine ⟨C, ?_⟩
  intro c A u K₀ K₁ hApprox
  rcases hApprox with ⟨ε, Aseq, useq, hε, hAsmooth, husmooth, hEll, hAH,
    hLH, hBound, _hAconv, hDconv⟩
  have hOuter : Metric.closedBall c ((R + S) / 2) ⊆ Metric.ball c S :=
    Metric.closedBall_subset_ball (by linarith)
  have hTarget : Metric.closedBall c (R / 2) ⊆ Metric.ball c R :=
    Metric.closedBall_subset_ball (by linarith)
  let Bseq : ℕ → ℝ≥0 := fun m ↦ C * ((K₁ + ε m) + (K₀ + ε m))
  have hBlim : Tendsto Bseq atTop (𝓝 (C * (K₁ + K₀))) := by
    have hc : Continuous (fun e : ℝ≥0 ↦ C * ((K₁ + e) + (K₀ + e))) := by fun_prop
    simpa [Bseq, Function.comp_def] using hc.continuousAt.tendsto.comp hε
  apply holderBoundOn_two_of_localJetLimit hBlim
  · intro m
    exact hSmooth Metric.isOpen_ball hOuter (hAsmooth m) (husmooth m) (hEll m)
      (hAH m) (hLH m) (hBound m)
  · intro j hj
    exact (hDconv j hj).mono hTarget

end CalabiYau.Schauder
