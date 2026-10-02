module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Orientation.FinitePartition
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.PartitionRefinement

/-!
# Finite positive atlases and their actual top-form integral

Lee, *Introduction to Smooth Manifolds*, 2nd ed., equation (16.2), p. 405,
and Proposition 16.6(a), p. 407. The linear map is constructed by summing
supported signed chart integrals. A bundled nonvanishing reference form fixes
the orientation, not a numerical multiplier. In a Kähler application that
reference is the correctly bundled and transported `ωⁿ/n!`.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

/-- A finite subordinate partition in restricted charts positive for the actual
smooth reference top form. Coverage and cross-chart compatibility follow from
these fields. No global integral or measure is part of the data. -/
structure FinitePositiveChartPartition
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) where
  charts : M → OrientedLocalChart d M
  partition : SmoothPartitionOfUnity M 𝓘(ℝ, Fin d → ℝ) M Set.univ
  indices : Finset M
  positive : ∀ i ∈ indices, (charts i).IsPositiveFor ν
  subordinate : ∀ i ∈ indices, tsupport (partition i) ⊆ (charts i).domain
  sum_eq_one : ∀ p : M, ∑ i ∈ indices, partition i p = 1

variable [T2Space M] [CompactSpace M]

/-- The existing positive finite-atlas theorem supplies the integration data. -/
theorem exists_finitePositiveChartPartition
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) :
    Nonempty (FinitePositiveChartPartition ν) := by
  obtain ⟨C, ρ, s, _hcenter, hpos, _hcompat, hsub, hsum⟩ :=
    exists_finite_oriented_chart_partition ν hν
  exact ⟨⟨C, ρ, s, fun i _ => hpos i, fun i _ => hsub i, hsum⟩⟩

omit [T2Space M] [CompactSpace M] in
theorem FinitePositiveChartPartition.localized_closedSupport
    {ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d}
    (A : FinitePositiveChartPartition ν)
    (i : M) (hi : i ∈ A.indices)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) :
    closure {p : M | smoothMulForm (A.partition i) η p ≠ 0} ⊆
      (A.charts i).domain := by
  exact ((smoothMulForm_closedSupport_subset (A.partition i) η).trans
    Set.inter_subset_left).trans (A.subordinate i hi)

/-- The actual finite-sum integral, real-linear because each summand is
supported in its chart and therefore has integrable coordinate coefficient. -/
def FinitePositiveChartPartition.integral
    {ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d}
    (A : FinitePositiveChartPartition ν) :
    DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d →ₗ[ℝ] ℝ where
  toFun := partitionChartIntegral A.charts A.partition A.indices
  map_add' η ζ := by
    unfold partitionChartIntegral
    simp_rw [smoothMulForm_add]
    calc
      (∑ i ∈ A.indices, signedChartIntegral (A.charts i)
          (smoothMulForm (A.partition i) η + smoothMulForm (A.partition i) ζ)) =
          ∑ i ∈ A.indices,
            (signedChartIntegral (A.charts i) (smoothMulForm (A.partition i) η) +
              signedChartIntegral (A.charts i) (smoothMulForm (A.partition i) ζ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact signedChartIntegral_add (A.charts i) _ _
          (A.localized_closedSupport i hi η) (A.localized_closedSupport i hi ζ)
      _ = _ := Finset.sum_add_distrib
  map_smul' c η := by
    unfold partitionChartIntegral
    simp_rw [smoothMulForm_smul, signedChartIntegral_smul]
    exact (Finset.mul_sum A.indices _ c).symm

omit [T2Space M] [CompactSpace M] in
/-- Smooth multiplication gives the actual weighted chart coefficient,
including its zero extension outside the target. -/
theorem chartTopCoefficient_smoothMulForm
    (f : C^∞⟮𝓘(ℝ, Fin d → ℝ), M; 𝓘(ℝ), ℝ⟯)
    (x : M) (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (y : Fin d → ℝ) :
    chartTopCoefficient x (smoothMulForm f η) y =
      f ((extChartAt 𝓘(ℝ, Fin d → ℝ) x).symm y) * chartTopCoefficient x η y := by
  classical
  unfold chartTopCoefficient
  split_ifs with hy
  · rw [continuousAlternatingMap_trivializationAt_apply,
      continuousAlternatingMap_trivializationAt_apply]
    change ((f ((extChartAt 𝓘(ℝ, Fin d → ℝ) x).symm y) •
      η ((extChartAt 𝓘(ℝ, Fin d → ℝ) x).symm y)).compContinuousLinearMap _)
      (fun j : Fin d => Pi.single j (1 : ℝ)) = _
    rw [ContinuousAlternatingMap.compContinuousLinearMap_smul]
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  · simp

/-- Numerical evaluation is the finite weighted signed coordinate integral,
with no additional reference-form, factorial, or power-of-two factor. -/
theorem FinitePositiveChartPartition.integral_apply_weighted
    {ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d}
    (A : FinitePositiveChartPartition ν)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) :
    A.integral η = ∑ i ∈ A.indices,
      ∫ y : Fin d → ℝ, (A.charts i).sign.val *
        (A.partition i ((extChartAt 𝓘(ℝ, Fin d → ℝ) (A.charts i).center).symm y) *
          chartTopCoefficient (A.charts i).center η y) ∂volume := by
  change partitionChartIntegral A.charts A.partition A.indices η = _
  unfold partitionChartIntegral
  apply Finset.sum_congr rfl
  intro i _hi
  unfold signedChartIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [chartTopCoefficient_smoothMulForm]

end CalabiYau.DifferentialForm
