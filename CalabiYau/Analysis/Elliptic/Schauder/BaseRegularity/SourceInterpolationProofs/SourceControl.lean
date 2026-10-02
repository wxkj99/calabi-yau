module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.BallHessian
public import CalabiYau.Mathlib.Analysis.Holder.Localization
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import CalabiYau.Mathlib.Analysis.Holder.Bilinear
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.FrozenPositiveDefinite
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
public import CalabiYau.Mathlib.Analysis.Holder.Scaling
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatSemigroup.Schauder
public import CalabiYau.Analysis.Estimates.Absorption
public import CalabiYau.Mathlib.Analysis.Holder.Interpolation
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.Basic

/-!
# Local source Holder/sup control and coefficient-extension restriction control.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem holderBoundOn_zero_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α K : ℝ≥0} {U s : Set E} {f : E → ℝ}
    (hsubset : s ⊆ U) (hbound : HolderBoundOn 0 α K U f) :
    HolderWith K α (s.domRestrict f) := by
  let L := continuousMultilinearCurryFin0 ℝ E ℝ
  have hlocal : HolderOnWith K α f U := by
    intro x hx y hy
    have h := hbound.2 x hx y hy
    rw [iteratedFDeriv_zero_eq_comp] at h
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
    rw [L.symm.edist_map] at h
    exact h
  rw [← holderOnWith_univ]
  intro x hx y hy
  simpa only [Set.domRestrict_apply, Subtype.edist_eq] using
    hlocal x.1 (hsubset x.2) y.1 (hsubset y.2)

theorem realBallSource_local_control
    {n : ℕ} {α lam K K₀ K₁ : ℝ≥0} {U : Set (RealBallModel n)}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ} {x : RealBallModel n} {δ : ℝ}
    (hball : Metric.closedBall x δ ⊆ U)
    (hdata : RealSmoothBallData α lam K K₀ K₁ U a u) :
    HolderWith K₁ α ((Metric.ball x δ).domRestrict (realBallSource a u)) ∧
    ∀ y ∈ Metric.ball x δ, ‖realBallSource a u y‖ ≤ K₁ := by
  have hsubset : Metric.ball x δ ⊆ U :=
    Metric.ball_subset_closedBall.trans hball
  refine ⟨holderBoundOn_zero_restrict hsubset hdata.source_holder, ?_⟩
  intro y hy
  have h := hdata.source_holder.1 0 (by omega) y (hsubset hy)
  simpa only [norm_iteratedFDeriv_zero] using h

theorem realBallCoefficientExtension_control
    {n : ℕ} {α K : ℝ≥0} {U : Set (RealBallModel n)}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {x : RealBallModel n} {δ : ℝ}
    (hball : Metric.closedBall x δ ⊆ U)
    (hcoeff : ∀ i j, HolderBoundOn 0 α K U (fun y => a y i j))
    (coeff : RealBallCoefficientExtension a x δ) :
    ∀ i j, HolderWith K α
      ((Metric.ball x δ).domRestrict (coeff.coefficient i j : RealBallModel n → ℝ)) := by
  intro i j
  let L := continuousMultilinearCurryFin0 ℝ (RealBallModel n) ℝ
  have hlocal : HolderOnWith K α (fun y => a y i j) (Metric.ball x δ) := by
    have h := (hcoeff i j).2
    intro y hy z hz
    have h' := h y (Metric.ball_subset_closedBall.trans hball hy)
      z (Metric.ball_subset_closedBall.trans hball hz)
    rw [iteratedFDeriv_zero_eq_comp] at h'
    change edist (L.symm (a y i j)) (L.symm (a z i j)) ≤ _ at h'
    rw [L.symm.edist_map] at h'
    exact h'
  have hcoeff' : HolderWith K α
      ((Metric.ball x δ).domRestrict (fun y => a y i j)) := by
    rw [← holderOnWith_univ]
    intro z hz w hw
    simpa only [Set.domRestrict_apply, Subtype.edist_eq] using
      hlocal z.1 z.2 w.1 w.2
  apply holderWith_congr hcoeff'
  intro z
  exact (coeff.agrees i j z.1 z.2).symm

theorem realBallCoefficientExtension_norm_control
    {n : ℕ} {α K : ℝ≥0} {U : Set (RealBallModel n)}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {x : RealBallModel n} {δ : ℝ}
    (hball : Metric.closedBall x δ ⊆ U)
    (hcoeff : ∀ i j, HolderBoundOn 0 α K U (fun y => a y i j))
    (coeff : RealBallCoefficientExtension a x δ) :
    ∀ i j y, y ∈ Metric.ball x δ → ‖coeff.coefficient i j y‖ ≤ K := by
  intro i j y hy
  have h := (hcoeff i j).1 0 (by omega) y
    (Metric.ball_subset_closedBall.trans hball hy)
  rw [coeff.agrees i j y hy]
  simpa only [norm_iteratedFDeriv_zero] using h

end CalabiYau.Schauder.SourceInterpolationProofs
