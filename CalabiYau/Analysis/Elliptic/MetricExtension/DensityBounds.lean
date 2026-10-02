-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/MetricExtension/DensityBounds.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.MetricExtension

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def densityOnEuclidClosureSup
    (g : SmoothRiemannianMetric I M) (α : M) (Ω' : Set EuclN) : ℝ :=
  sSup ((fun x => |densityOnEuclid (I := I) g α x|) '' closure Ω')

lemma densityOnEuclidClosureSup_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (Ω' : Set EuclN) :
    0 ≤ densityOnEuclidClosureSup (I := I) (M := M) g α Ω' := by
  unfold densityOnEuclidClosureSup
  refine Real.sSup_nonneg ?_
  rintro y ⟨x, _, rfl⟩
  exact abs_nonneg _

lemma abs_densityOnEuclid_le_closureSup
    {g : SmoothRiemannianMetric I M} {α : M} {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {x : EuclN} (hx : x ∈ closure Ω') :
    |densityOnEuclid (I := I) g α x| ≤
      densityOnEuclidClosureSup (I := I) (M := M) g α Ω' := by
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (closure Ω') :=
    ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mono hΩ'_closure_in
  have h_abs_contOn : ContinuousOn
      (fun x => |densityOnEuclid (I := I) g α x|) (closure Ω') :=
    h_dens_contOn.abs
  have h_bddAbove : BddAbove
      ((fun x => |densityOnEuclid (I := I) g α x|) '' closure Ω') :=
    hΩ'_closure_compact.bddAbove_image h_abs_contOn
  exact le_csSup h_bddAbove (Set.mem_image_of_mem _ hx)

lemma densityOnEuclid_mul_memLp
    {g : SmoothRiemannianMetric I M} {α : M} {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict (closure Ω'))) :
    MemLp (fun x => densityOnEuclid (I := I) g α x * f x) 2
      ((volume : Measure EuclN).restrict (closure Ω')) := by
  classical
  have hΩ'_closure_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (closure Ω') :=
    ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mono hΩ'_closure_in
  have h_dens_aesm : AEStronglyMeasurable (densityOnEuclid (I := I) g α)
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    h_dens_contOn.aestronglyMeasurable hΩ'_closure_meas
  set Mden : ℝ := densityOnEuclidClosureSup (I := I) (M := M) g α Ω' with hMden_def
  have hMden_nn : 0 ≤ Mden :=
    densityOnEuclidClosureSup_nonneg (I := I) (M := M) g α Ω'
  have h_pt_le : ∀ᵐ x ∂((volume : Measure EuclN).restrict (closure Ω')),
      ‖densityOnEuclid (I := I) g α x * f x‖ ≤ ‖Mden * f x‖ := by
    refine ae_restrict_of_forall_mem hΩ'_closure_meas ?_
    intro x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hMden_nn]
    have h_dens_bd : |densityOnEuclid (I := I) g α x| ≤ Mden :=
      abs_densityOnEuclid_le_closureSup
        hΩ'_closure_compact hΩ'_closure_in hx
    exact mul_le_mul_of_nonneg_right h_dens_bd (abs_nonneg _)
  exact MemLp.mono (hf.const_mul Mden)
    (h_dens_aesm.mul hf.aestronglyMeasurable) h_pt_le

lemma eLpNorm_densityOnEuclid_mul_sq_le
    {g : SmoothRiemannianMetric I M} {α : M} {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict (closure Ω'))) :
    (eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
      (densityOnEuclidClosureSup (I := I) (M := M) g α Ω') ^ 2 *
        (eLpNorm f 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 := by
  classical
  have hΩ'_closure_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  set μ : Measure EuclN := (volume : Measure EuclN).restrict (closure Ω')
    with hμ_def
  set Mden : ℝ := densityOnEuclidClosureSup (I := I) (M := M) g α Ω' with hMden_def
  have hMden_nn : 0 ≤ Mden :=
    densityOnEuclidClosureSup_nonneg (I := I) (M := M) g α Ω'
  have h_pt_le : ∀ᵐ x ∂μ,
      ‖densityOnEuclid (I := I) g α x * f x‖ ≤ ‖(Mden • f) x‖ := by
    rw [hμ_def]
    refine ae_restrict_of_forall_mem hΩ'_closure_meas ?_
    intro x hx
    change ‖densityOnEuclid (I := I) g α x * f x‖ ≤ ‖Mden • f x‖
    rw [Real.norm_eq_abs, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hMden_nn]
    have h_dens_bd : |densityOnEuclid (I := I) g α x| ≤ Mden :=
      abs_densityOnEuclid_le_closureSup
        hΩ'_closure_compact hΩ'_closure_in hx
    exact mul_le_mul_of_nonneg_right h_dens_bd (abs_nonneg _)
  have h_eLp_le :
      eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ ≤
        (‖Mden‖ₑ : ℝ≥0∞) * eLpNorm f 2 μ := by
    calc eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ
        ≤ eLpNorm (Mden • f) 2 μ := eLpNorm_mono_ae h_pt_le
      _ = (‖Mden‖ₑ : ℝ≥0∞) * eLpNorm f 2 μ := eLpNorm_const_smul Mden f 2 μ
  have h_eLpf_ne_top : eLpNorm f 2 μ ≠ (⊤ : ℝ≥0∞) := by
    rw [hμ_def]; exact hf.2.ne
  have h_toReal_le :
      (eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ).toReal ≤
        Mden * (eLpNorm f 2 μ).toReal := by
    have h_mono := ENNReal.toReal_mono
      (by
        rw [hμ_def]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top hf.2.ne) h_eLp_le
    rwa [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
      abs_of_nonneg hMden_nn] at h_mono
  have h_lhs_nn : 0 ≤
      (eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ).toReal :=
    ENNReal.toReal_nonneg
  have h_rhs_nn : 0 ≤ Mden * (eLpNorm f 2 μ).toReal :=
    mul_nonneg hMden_nn ENNReal.toReal_nonneg
  calc (eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ).toReal ^ 2
      ≤ (Mden * (eLpNorm f 2 μ).toReal) ^ 2 := by
        exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
    _ = Mden ^ 2 * (eLpNorm f 2 μ).toReal ^ 2 := by ring

end CalabiYau.Laplacian.MetricExtension
