module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.SuccessorSource
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

namespace PreviousForcingProductsUnique
open Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP

abbrev Kα (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

abbrev Ωα (α : M) : Set EuclN :=
  chartTargetEuclid (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_compact (α : M) :
    IsCompact (Kα (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma Kα_subset_Ωα (α : M) :
    Kα (I := I) (M := M) α ⊆ Ωα (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma Ωα_isOpen (α : M) : IsOpen (Ωα (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chosenWeakPartialOrZero_ae_zero_on_open_sub_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact Sobolev.Euclidean.HasWeakPartialDeriv.restrict hV_sub hg_weak
  have h_partial_V : Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V) u V :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu_V i
  have h_partial_Ω : Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu i
  have h_partial_Ω_V : Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) u V :=
    Sobolev.Euclidean.HasWeakPartialDeriv.restrict hV_sub h_partial_Ω
  have h_chosen_V_zero :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartialOrZero_memLp_of_mem hu i
  have hg_lp_Ω_V : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_local_Ω_V : LocallyIntegrable
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartialOrZero_memLp_of_mem hu_V i
  have hgV_local : LocallyIntegrable
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V :=
    Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_local_Ω_V hgV_local
  exact h_unique.trans h_chosen_V_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_coef_mul_factor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef (Ωα (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (Ωα (I := I) (M := M) α))
    (hfactor_ae_zero : factor =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (Ωα (I := I) (M := M) α) := by
  classical
  obtain ⟨δ, coef_ext, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := coef) α hcoef_chart
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  obtain ⟨ε, χ, hε_pos, hε_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef_ext y) :=
    hχ_smooth.mul hExt_smooth
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef_ext y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef_ext y) * factor y) (Ωα (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  set ρ : ℝ := min δ ε with hρ_def
  have hρ_pos : 0 < ρ := lt_min hδ_pos hε_pos
  have hρ_le_δ : ρ ≤ δ := min_le_left _ _
  have hρ_le_ε : ρ ≤ ε := min_le_right _ _
  set Cρ : Set EuclN := Metric.cthickening ρ (Kα (I := I) (M := M) α) with hCρ_def
  have hCρ_sub_Cδ : Cρ ⊆ Metric.cthickening δ (Kα (I := I) (M := M) α) :=
    Metric.cthickening_mono hρ_le_δ _
  have hCρ_sub_Cε : Cρ ⊆ Metric.cthickening ε (Kα (I := I) (M := M) α) :=
    Metric.cthickening_mono hρ_le_ε _
  have hCρ_in_target : Cρ ⊆ Ωα (I := I) (M := M) α := hCρ_sub_Cδ.trans hδ_in
  have h_ae_eq : (fun y => (χ y * coef_ext y) * factor y) =ᵐ[
      (volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    set Ω : Set EuclN := Ωα (I := I) (M := M) α
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hCρ_closed : IsClosed Cρ := Metric.isClosed_cthickening
    have hCρ_meas : MeasurableSet Cρ := hCρ_closed.measurableSet
    have h_eq_on_Cρ : (fun y => (χ y * coef_ext y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cρ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCρ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hy_Cδ : y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α) :=
        hCρ_sub_Cδ hy
      have hy_Cε : y ∈ Metric.cthickening ε (Kα (I := I) (M := M) α) :=
        hCρ_sub_Cε hy
      have hχy : χ y = 1 := hχ_one y hy_Cε
      have h_coef : coef_ext y = coef y := hExt_eq y hy_Cδ
      change (χ y * coef_ext y) * factor y = coef y * factor y
      rw [hχy, h_coef]; ring
    have hKα_in_Cρ : Kα (I := I) (M := M) α ⊆ Cρ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cρ ⊆ Ω \ Kα (I := I) (M := M) α := by
      intro y hy
      exact ⟨hy.1, fun hyK => hy.2 (hKα_in_Cρ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cρ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cρ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα (I := I) (M := M) α) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff :
        (fun y => (χ y * coef_ext y) * factor y) =ᵐ[
          (volume : Measure EuclN).restrict (Ω \ Cρ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef_ext y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef_ext y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cρ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cρ) ≪
          (volume : Measure EuclN).restrict Cρ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cρ
    have h_diff_meas : MeasurableSet (Ω \ Cρ) := hΩ_meas.diff hCρ_meas
    have h_cover : Ω = (Ω ∩ Cρ) ∪ (Ω \ Cρ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cρ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cρ) (Ω \ Cρ) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cρ) ∪ (Ω \ Cρ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α) h_ae_eq).mp
    h_prod_memWkp

omit [NeZero (Module.finrank ℝ E)] in
theorem previous_value_product_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (K : ℕ)
    (l : Fin (Module.finrank ℝ E))
    (prev_fChartEffective : EuclN → ℝ)
    (h_prev_memWkp_K :
      MemWkp (d := Module.finrank ℝ E) K 2 prev_fChartEffective
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEffective =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α l y * prev_fChartEffective y)
      (Ωα (I := I) (M := M) α) := by
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l)
        (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) (M := M) g α l
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_prev_memWkp_K h_prev_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem previous_gradient_product_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (K : ℕ)
    (l : Fin (Module.finrank ℝ E))
    (prev_fChartEffective : EuclN → ℝ)
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEffective
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEffective =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l prev_fChartEffective
          (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityOnEuclid (I := I) g α)
        (Ωα (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l prev_fChartEffective
          (Ωα (I := I) (M := M) α))
        (Ωα (I := I) (M := M) α) :=
    h_prev_memWkp_succ.chosenWeakPartial_mem l
  have h_prev_memW1p : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEffective (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEffective
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_diff_open : IsOpen
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  have h_diff_subset :
      Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
        Ωα (I := I) (M := M) α := fun _ hy => hy.1
  have h_factor_ae_zero :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l prev_fChartEffective
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_on_open_sub_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) h_diff_open h_diff_subset
      h_prev_memW1p h_prev_ae_zero l
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem previous_forcing_products_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (K : ℕ)
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E))
    (h_previous_memWkp : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      previousForcing (chartTargetEuclid (I := I) (M := M) α))
    (h_previous_ae_zero : previousForcing =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α l y * previousForcing y)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityOnEuclid (I := I) g α y *
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l previousForcing
          (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  exact ⟨previous_value_product_memWkp (I := I) (M := M) g α K l previousForcing
    (h_previous_memWkp.le_of_le (by omega)) h_previous_ae_zero,
    previous_gradient_product_memWkp (I := I) (M := M) g α K l previousForcing
      h_previous_memWkp h_previous_ae_zero⟩

#print axioms previous_forcing_products_memWkp
#print axioms previous_value_product_memWkp
#print axioms previous_gradient_product_memWkp

end PreviousForcingProductsUnique
end CalabiYau.PoissonDomainRegularity
