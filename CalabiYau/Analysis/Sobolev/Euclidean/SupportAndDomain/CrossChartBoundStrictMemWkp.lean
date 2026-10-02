-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/SupportAndDomain/CrossChartBoundStrictMemWkp.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrict
public import CalabiYau.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartIdentity
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev

namespace Euclidean

private lemma indicator_eq_of_tsupport_subset
    {α : Type*} [Zero α]
    {X : Type*} [TopologicalSpace X] {f : X → α}
    {Ω Ω' : Set X} (hΩΩ' : Ω' ⊆ Ω)
    (hf_support : tsupport f ⊆ Ω') :
    Ω.indicator f = Ω'.indicator f := by
  funext x
  by_cases hxΩ' : x ∈ Ω'
  · simp [Set.indicator_of_mem hxΩ', Set.indicator_of_mem (hΩΩ' hxΩ')]
  · simp only [Set.indicator_of_notMem hxΩ']
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
      have hx_off : x ∉ tsupport f := fun h => hxΩ' (hf_support h)
      exact image_eq_zero_of_notMem_tsupport hx_off
    · simp [Set.indicator_of_notMem hxΩ]

private lemma eLpNorm_restrict_eq_of_tsupport_subset_aux
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}
    {α : Type*} [NormedAddCommGroup α] {p : ℝ≥0∞}
    {f : X → α}
    {Ω Ω' : Set X} (hΩ_meas : MeasurableSet Ω) (hΩ'_meas : MeasurableSet Ω')
    (hΩΩ' : Ω' ⊆ Ω) (hf_support : tsupport f ⊆ Ω') :
    eLpNorm f p (μ.restrict Ω) = eLpNorm f p (μ.restrict Ω') := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hΩ'_meas]
  rw [indicator_eq_of_tsupport_subset hΩΩ' hf_support]

private lemma eLpNorm_restrict_eq_of_ae_zero_off
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {α : Type*} [NormedAddCommGroup α] {p : ℝ≥0∞}
    {f : X → α}
    {Ω Ω' : Set X} (hΩ_meas : MeasurableSet Ω) (hΩ'_meas : MeasurableSet Ω')
    (hΩΩ' : Ω' ⊆ Ω)
    (hf_zero : ∀ᵐ x ∂(μ.restrict (Ω \ Ω')), f x = 0) :
    eLpNorm f p (μ.restrict Ω) = eLpNorm f p (μ.restrict Ω') := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hΩ'_meas]
  have h_ae : Ω.indicator f =ᵐ[μ] Ω'.indicator f := by
    have h_meas_diff : MeasurableSet (Ω \ Ω') := hΩ_meas.diff hΩ'_meas
    have h_ae_diff : ∀ᵐ x ∂(μ.restrict (Ω \ Ω')), Ω.indicator f x = Ω'.indicator f x := by
      filter_upwards [hf_zero] with x hx_zero
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]
        by_cases hxΩ' : x ∈ Ω'
        · rw [Set.indicator_of_mem hxΩ']
        · rw [Set.indicator_of_notMem hxΩ']; exact hx_zero
      · rw [Set.indicator_of_notMem hxΩ]
        have hxΩ'_neg : x ∉ Ω' := fun h => hxΩ (hΩΩ' h)
        rw [Set.indicator_of_notMem hxΩ'_neg]
    have h_ae_compl : ∀ᵐ x ∂(μ.restrict ((Ω \ Ω')ᶜ)), Ω.indicator f x = Ω'.indicator f x := by
      have h_meas_compl : MeasurableSet (Ω \ Ω')ᶜ := h_meas_diff.compl
      refine (ae_restrict_iff' h_meas_compl).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      by_cases hxΩ : x ∈ Ω
      · have hxΩ' : x ∈ Ω' := by
          by_contra hxΩ'_neg
          exact hx ⟨hxΩ, hxΩ'_neg⟩
        rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ']
      · rw [Set.indicator_of_notMem hxΩ]
        have hxΩ'_neg : x ∉ Ω' := fun h => hxΩ (hΩΩ' h)
        rw [Set.indicator_of_notMem hxΩ'_neg]
    have hμ_split : μ.restrict (Ω \ Ω') + μ.restrict (Ω \ Ω')ᶜ = μ :=
      Measure.restrict_add_restrict_compl h_meas_diff
    have h_ae' : Ω.indicator f =ᵐ[μ.restrict (Ω \ Ω') + μ.restrict (Ω \ Ω')ᶜ]
        Ω'.indicator f := by
      rw [Filter.EventuallyEq, ae_add_measure_iff]
      exact ⟨h_ae_diff, h_ae_compl⟩
    rw [← hμ_split]
    exact h_ae'
  exact eLpNorm_congr_ae h_ae

lemma wkpNorm_eq_of_tsupport_subset_one
    {d : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) 1 p u Ω) (hu_support : tsupport u ⊆ Ω') :
    MemWkp (d := d) 1 p u Ω' ∧
    iteratedWeakSobolevNorm (d := d) 1 p u Ω = iteratedWeakSobolevNorm (d := d) 1 p u Ω' := by
  classical
  have hu_W1p_Ω : DeGiorgi.MemW1p (d := d) p u Ω := hu.memW1p
  have hu_witness_Ω : DeGiorgi.MemW1pWitness (d := d) p u Ω :=
    hu_W1p_Ω.someWitness
  have hu_witness_Ω' : DeGiorgi.MemW1pWitness (d := d) p u Ω' :=
    DeGiorgi.MemW1pWitness.restrict (d := d) hΩ' hΩΩ' hu_witness_Ω
  have hu_W1p_Ω' : DeGiorgi.MemW1p (d := d) p u Ω' := hu_witness_Ω'.memW1p
  have hu_mem_Ω' : MemWkp (d := d) 1 p u Ω' :=
    MemWkp.one_iff_memW1p.mpr hu_W1p_Ω'
  refine ⟨hu_mem_Ω', ?_⟩
  have h_partial_ae : ∀ i : Fin d,
      chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict Ω']
        chosenWeakPartialOrZero (d := d) p i u Ω' := by
    intro i
    have hP_Ω :=
      chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu_W1p_Ω i
    have hP_Ω' :=
      chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu_W1p_Ω' i
    have hP_Ω_restricted : DeGiorgi.HasWeakPartialDeriv i
        (chosenWeakPartialOrZero (d := d) p i u Ω) u Ω' :=
      DeGiorgi.HasWeakPartialDeriv.restrict (d := d) hΩ' hΩΩ' hP_Ω
    have hP_Ω_local : LocallyIntegrable
        (chosenWeakPartialOrZero (d := d) p i u Ω) (volume.restrict Ω') := by
      have hmem : MeasureTheory.MemLp
          (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) :=
        chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_W1p_Ω i
      have hmem' : MeasureTheory.MemLp
          (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω') :=
        hmem.mono_measure (Measure.restrict_mono_set volume hΩΩ')
      exact hmem'.locallyIntegrable hp_one
    have hP_Ω'_local : LocallyIntegrable
        (chosenWeakPartialOrZero (d := d) p i u Ω') (volume.restrict Ω') := by
      have hmem : MeasureTheory.MemLp
          (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') :=
        chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_W1p_Ω' i
      exact hmem.locallyIntegrable hp_one
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ' hP_Ω_restricted hP_Ω'
      hP_Ω_local hP_Ω'_local
  set U : Set (EuclideanSpace ℝ (Fin d)) := Ω \ tsupport u with hU_def
  have hU_open : IsOpen U := hΩ.sdiff (isClosed_tsupport _)
  have hU_subset : U ⊆ Ω := fun x hx => hx.1
  have hu_zero_on_U : ∀ x ∈ U, u x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport hx.2
  have hZero_isWeakPartial : ∀ i : Fin d,
      DeGiorgi.HasWeakPartialDeriv (d := d) i (fun _ => (0 : ℝ)) u U := by
    intro i φ hφ_smooth hφ_support hφ_sub
    have h_integrand_zero : ∀ᵐ x ∂(volume.restrict U),
        u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hU_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      rw [hu_zero_on_U x hx]; ring
    have hint_lhs : ∫ x in U, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 :=
      integral_eq_zero_of_ae h_integrand_zero
    rw [hint_lhs]
    have hzero : ∀ x, (0 : ℝ) * φ x = 0 := fun x => zero_mul _
    simp [hzero]
  have hP_Ω_restricted_U : ∀ i : Fin d,
      DeGiorgi.HasWeakPartialDeriv (d := d) i
        (chosenWeakPartialOrZero (d := d) p i u Ω) u U := fun i =>
    DeGiorgi.HasWeakPartialDeriv.restrict (d := d) hU_open hU_subset
      (chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu_W1p_Ω i)
  have hZero_local_U : LocallyIntegrable
        (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (volume.restrict U) :=
    locallyIntegrable_const (μ := volume.restrict U) (0 : ℝ)
  have hP_Ω_local_U : ∀ i : Fin d, LocallyIntegrable
      (chosenWeakPartialOrZero (d := d) p i u Ω) (volume.restrict U) := by
    intro i
    have hmem : MeasureTheory.MemLp
        (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) :=
      chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_W1p_Ω i
    have hmem' : MeasureTheory.MemLp
        (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict U) :=
      hmem.mono_measure (Measure.restrict_mono_set volume hU_subset)
    exact hmem'.locallyIntegrable hp_one
  have h_partial_zero_ae_U : ∀ i : Fin d,
      chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict U]
        (fun _ => (0 : ℝ)) := fun i =>
    DeGiorgi.HasWeakPartialDeriv.ae_eq hU_open
      (hP_Ω_restricted_U i) (hZero_isWeakPartial i)
      (hP_Ω_local_U i) hZero_local_U
  have h_diff_subset_U : Ω \ Ω' ⊆ U := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro h_in_support
    exact hx.2 (hu_support h_in_support)
  have h_partial_zero_ae_diff : ∀ i : Fin d,
      chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict (Ω \ Ω')]
        (fun _ => (0 : ℝ)) := by
    intro i
    have h_meas_diff : MeasurableSet (Ω \ Ω') :=
      hΩ.measurableSet.diff hΩ'.measurableSet
    have h_restrict_eq :
        (volume.restrict U).restrict (Ω \ Ω') = volume.restrict (Ω \ Ω') := by
      rw [Measure.restrict_restrict h_meas_diff]
      rw [Set.inter_eq_left.mpr h_diff_subset_U]
    have h := h_partial_zero_ae_U i
    have h_restricted := h.restrict (s := Ω \ Ω')
    rw [h_restrict_eq] at h_restricted
    exact h_restricted
  have h_u_zero_on_diff : ∀ x ∈ Ω \ Ω', u x = 0 := by
    intro x hx
    have hx_off : x ∉ tsupport u := fun h => hx.2 (hu_support h)
    exact image_eq_zero_of_notMem_tsupport hx_off
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  have h_split : Ω = Ω' ∪ (Ω \ Ω') := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      by_cases hxΩ' : x ∈ Ω'
      · exact Or.inl hxΩ'
      · exact Or.inr ⟨hx, hxΩ'⟩
    · intro x hx
      rcases hx with hxΩ' | hx_diff
      · exact hΩΩ' hxΩ'
      · exact hx_diff.1
  have h_disj : Disjoint Ω' (Ω \ Ω') := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact hx'.2 hx
  have h_meas_diff : MeasurableSet (Ω \ Ω') :=
    hΩ.measurableSet.diff hΩ'.measurableSet
  have h_u_eLp_eq : eLpNorm u p (volume.restrict Ω) =
      eLpNorm u p (volume.restrict Ω') := by
    have hu_zero_diff : ∀ᵐ x ∂(volume.restrict (Ω \ Ω')), u x = 0 := by
      refine (ae_restrict_iff' h_meas_diff).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact h_u_zero_on_diff x hx
    exact eLpNorm_restrict_eq_of_ae_zero_off
      hΩ.measurableSet hΩ'.measurableSet hΩΩ' hu_zero_diff
  have h_partial_eLp_eq : ∀ i : Fin d,
      eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) =
        eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') := by
    intro i
    have h_partial_diff_zero : ∀ᵐ x ∂(volume.restrict (Ω \ Ω')),
        chosenWeakPartialOrZero (d := d) p i u Ω x = 0 :=
      h_partial_zero_ae_diff i
    have h_eLp_Ω_eq_Ω' : eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p
          (volume.restrict Ω) =
        eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p
          (volume.restrict Ω') :=
      eLpNorm_restrict_eq_of_ae_zero_off
        hΩ.measurableSet hΩ'.measurableSet hΩΩ' h_partial_diff_zero
    have h_eLp_partials_eq :
        eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω') =
          eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') :=
      eLpNorm_congr_ae (h_partial_ae i)
    rw [h_eLp_Ω_eq_Ω', h_eLp_partials_eq]
  unfold iteratedWeakSobolevNorm
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
    fun α => by funext i; exact i.elim0
  have : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (h0_unique α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω') p (volume.restrict Ω'))]
  simp only [iterWeakPartial_zero]
  rw [h_u_eLp_eq]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro α _
  have h_iter1_Ω :
      iterWeakPartial (d := d) p 1 α u Ω =
      chosenWeakPartialOrZero (d := d) p (α 0) u Ω := by
    rw [iterWeakPartial_succ]; rfl
  have h_iter1_Ω' :
      iterWeakPartial (d := d) p 1 α u Ω' =
      chosenWeakPartialOrZero (d := d) p (α 0) u Ω' := by
    rw [iterWeakPartial_succ]; rfl
  rw [h_iter1_Ω, h_iter1_Ω']
  exact h_partial_eLp_eq (α 0)

lemma wkpNorm_le_of_tsupport_subset_mem_small_one
    {d : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) 1 p u Ω') (hu_support : tsupport u ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) 1 p u Ω ≤ iteratedWeakSobolevNorm (d := d) 1 p u Ω' := by
  classical
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  have hu_W1p_Ω' : DeGiorgi.MemW1p (d := d) p u Ω' := hu.memW1p
  have hu_L_Ω' : MeasureTheory.MemLp u p (volume.restrict Ω') := hu.memLp
  have hu_zero_diff : ∀ x ∈ Ω \ Ω', u x = 0 := by
    intro x hx
    have hx_off : x ∉ tsupport u := fun h => hx.2 (hu_support h)
    exact image_eq_zero_of_notMem_tsupport hx_off
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_meas_diff : MeasurableSet (Ω \ Ω') := hΩ_meas.diff hΩ'_meas
  have h_split : Ω = Ω' ∪ (Ω \ Ω') := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      by_cases hxΩ' : x ∈ Ω'
      · exact Or.inl hxΩ'
      · exact Or.inr ⟨hx, hxΩ'⟩
    · intro x hx
      rcases hx with hxΩ' | hx_diff
      · exact hΩΩ' hxΩ'
      · exact hx_diff.1
  have h_disj : Disjoint Ω' (Ω \ Ω') := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact hx'.2 hx
  have hu_diff_strongly : AEStronglyMeasurable u (volume.restrict (Ω \ Ω')) := by
    have h_eq : u =ᵐ[volume.restrict (Ω \ Ω')] (fun _ => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_meas_diff).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hu_zero_diff x hx
    have h_zero_meas : AEStronglyMeasurable (fun (_ : EuclideanSpace ℝ (Fin d)) => (0 : ℝ))
        (volume.restrict (Ω \ Ω')) := aestronglyMeasurable_const
    exact h_zero_meas.congr h_eq.symm
  have h_u_eLp_eq : eLpNorm u p (volume.restrict Ω) =
      eLpNorm u p (volume.restrict Ω') := by
    have hu_zero_diff_ae : ∀ᵐ x ∂(volume.restrict (Ω \ Ω')), u x = 0 := by
      refine (ae_restrict_iff' h_meas_diff).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hu_zero_diff x hx
    exact eLpNorm_restrict_eq_of_ae_zero_off
      hΩ_meas hΩ'_meas hΩΩ' hu_zero_diff_ae
  have h_partial_le : ∀ i : Fin d,
      eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) ≤
        eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') := by
    intro i
    by_cases hu_Ω : DeGiorgi.MemW1p (d := d) p u Ω
    · have hP_Ω :=
        chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu_Ω i
      have hP_Ω' :=
        chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu_W1p_Ω' i
      have hP_Ω_restricted : DeGiorgi.HasWeakPartialDeriv i
          (chosenWeakPartialOrZero (d := d) p i u Ω) u Ω' :=
        DeGiorgi.HasWeakPartialDeriv.restrict (d := d) hΩ' hΩΩ' hP_Ω
      have hP_Ω_local_Ω' : LocallyIntegrable
          (chosenWeakPartialOrZero (d := d) p i u Ω) (volume.restrict Ω') := by
        have hmem : MeasureTheory.MemLp
            (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) :=
          chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_Ω i
        have hmem' : MeasureTheory.MemLp
            (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω') :=
          hmem.mono_measure (Measure.restrict_mono_set volume hΩΩ')
        exact hmem'.locallyIntegrable hp_one
      have hP_Ω'_local_Ω' : LocallyIntegrable
          (chosenWeakPartialOrZero (d := d) p i u Ω') (volume.restrict Ω') := by
        have hmem : MeasureTheory.MemLp
            (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') :=
          chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_W1p_Ω' i
        exact hmem.locallyIntegrable hp_one
      have h_partials_ae :
          chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict Ω']
            chosenWeakPartialOrZero (d := d) p i u Ω' :=
        DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ' hP_Ω_restricted hP_Ω'
          hP_Ω_local_Ω' hP_Ω'_local_Ω'
      set U : Set (EuclideanSpace ℝ (Fin d)) := Ω \ tsupport u
      have hU_open : IsOpen U := hΩ.sdiff (isClosed_tsupport _)
      have hU_subset : U ⊆ Ω := fun x hx => hx.1
      have hu_zero_on_U : ∀ x ∈ U, u x = 0 := by
        intro x hx
        exact image_eq_zero_of_notMem_tsupport hx.2
      have hZero_isWeakPartial : DeGiorgi.HasWeakPartialDeriv (d := d) i
          (fun _ => (0 : ℝ)) u U := by
        intro φ hφ_smooth hφ_support hφ_sub
        have h_integrand_zero : ∀ᵐ x ∂(volume.restrict U),
            u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
          refine (ae_restrict_iff' hU_open.measurableSet).mpr ?_
          refine Filter.Eventually.of_forall ?_
          intro x hx
          rw [hu_zero_on_U x hx]; ring
        have hint_lhs : ∫ x in U, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 :=
          integral_eq_zero_of_ae h_integrand_zero
        rw [hint_lhs]
        have hzero : ∀ x, (0 : ℝ) * φ x = 0 := fun x => zero_mul _
        simp [hzero]
      have hP_Ω_restricted_U : DeGiorgi.HasWeakPartialDeriv (d := d) i
          (chosenWeakPartialOrZero (d := d) p i u Ω) u U :=
        DeGiorgi.HasWeakPartialDeriv.restrict (d := d) hU_open hU_subset hP_Ω
      have hZero_local_U : LocallyIntegrable
          (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (volume.restrict U) :=
        locallyIntegrable_const (μ := volume.restrict U) (0 : ℝ)
      have hP_Ω_local_U : LocallyIntegrable
          (chosenWeakPartialOrZero (d := d) p i u Ω) (volume.restrict U) := by
        have hmem : MeasureTheory.MemLp
            (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) :=
          chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_Ω i
        have hmem' : MeasureTheory.MemLp
            (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict U) :=
          hmem.mono_measure (Measure.restrict_mono_set volume hU_subset)
        exact hmem'.locallyIntegrable hp_one
      have h_partial_zero_ae_U :
          chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict U]
            (fun _ => (0 : ℝ)) :=
        DeGiorgi.HasWeakPartialDeriv.ae_eq hU_open
          hP_Ω_restricted_U hZero_isWeakPartial hP_Ω_local_U hZero_local_U
      have h_diff_subset_U : Ω \ Ω' ⊆ U := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        intro h_in_support
        exact hx.2 (hu_support h_in_support)
      have h_partial_zero_ae_diff :
          chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict (Ω \ Ω')]
            (fun _ => (0 : ℝ)) := by
        have h_restrict_eq :
            (volume.restrict U).restrict (Ω \ Ω') = volume.restrict (Ω \ Ω') := by
          rw [Measure.restrict_restrict h_meas_diff]
          rw [Set.inter_eq_left.mpr h_diff_subset_U]
        have h_restricted := h_partial_zero_ae_U.restrict (s := Ω \ Ω')
        rw [h_restrict_eq] at h_restricted
        exact h_restricted
      have h_eLp_Ω_eq_Ω' :
          eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) =
          eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω') :=
        eLpNorm_restrict_eq_of_ae_zero_off
          hΩ_meas hΩ'_meas hΩΩ' h_partial_zero_ae_diff
      have h_eLp_partials_eq :
          eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω') =
          eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') :=
        eLpNorm_congr_ae h_partials_ae
      rw [h_eLp_Ω_eq_Ω', h_eLp_partials_eq]
    · rw [chosenWeakPartialOrZero_of_not_mem hu_Ω]
      rw [eLpNorm_zero]
      exact zero_le
  unfold iteratedWeakSobolevNorm
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
    fun α => by funext i; exact i.elim0
  have : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (h0_unique α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω') p (volume.restrict Ω'))]
  simp only [iterWeakPartial_zero]
  rw [h_u_eLp_eq]
  refine add_le_add (le_refl _) ?_
  refine Finset.sum_le_sum ?_
  intro α _
  have h_iter1_Ω :
      iterWeakPartial (d := d) p 1 α u Ω =
      chosenWeakPartialOrZero (d := d) p (α 0) u Ω := by
    rw [iterWeakPartial_succ]; rfl
  have h_iter1_Ω' :
      iterWeakPartial (d := d) p 1 α u Ω' =
      chosenWeakPartialOrZero (d := d) p (α 0) u Ω' := by
    rw [iterWeakPartial_succ]; rfl
  rw [h_iter1_Ω, h_iter1_Ω']
  exact h_partial_le (α 0)

private lemma chosenWeakPartial_ae_eq_on_subset
    {d : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (_hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : DeGiorgi.MemW1p (d := d) p u Ω) (i : Fin d) :
    chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict Ω']
      chosenWeakPartialOrZero (d := d) p i u Ω' := by
  classical
  have hu_Ω' : DeGiorgi.MemW1p (d := d) p u Ω' :=
    DeGiorgi.MemW1pWitness.restrict (d := d) hΩ' hΩΩ' hu.someWitness |>.memW1p
  have hP_Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu i
  have hP_Ω' :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hu_Ω' i
  have hP_Ω_restricted : DeGiorgi.HasWeakPartialDeriv (d := d) i
      (chosenWeakPartialOrZero (d := d) p i u Ω) u Ω' :=
    DeGiorgi.HasWeakPartialDeriv.restrict (d := d) hΩ' hΩΩ' hP_Ω
  have hP_Ω_local_Ω' : LocallyIntegrable
      (chosenWeakPartialOrZero (d := d) p i u Ω) (volume.restrict Ω') := by
    have hmem : MeasureTheory.MemLp
        (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) :=
      chosenWeakPartialOrZero_memLp_of_mem (d := d) hu i
    have hmem' : MeasureTheory.MemLp
        (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω') :=
      hmem.mono_measure (Measure.restrict_mono_set volume hΩΩ')
    exact hmem'.locallyIntegrable hp_one
  have hP_Ω'_local_Ω' : LocallyIntegrable
      (chosenWeakPartialOrZero (d := d) p i u Ω') (volume.restrict Ω') := by
    have hmem : MeasureTheory.MemLp
        (chosenWeakPartialOrZero (d := d) p i u Ω') p (volume.restrict Ω') :=
      chosenWeakPartialOrZero_memLp_of_mem (d := d) hu_Ω' i
    exact hmem.locallyIntegrable hp_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ' hP_Ω_restricted hP_Ω'
    hP_Ω_local_Ω' hP_Ω'_local_Ω'

private lemma iterWeakPartial_ae_eq_of_ae_zero_open_subset
    {d : ℕ}
    {h : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' U : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hU_open : IsOpen U)
    (hΩΩ' : Ω' ⊆ Ω) (hU_sub : U ⊆ Ω) (_hU_contains : Ω \ Ω' ⊆ U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu_mem : MemWkp (d := d) h p u Ω)
    (hu_zero : u =ᵐ[volume.restrict U] (fun _ => 0))
    (α : Fin h → Fin d) :
    iterWeakPartial (d := d) p h α u Ω =ᵐ[volume.restrict Ω']
      iterWeakPartial (d := d) p h α u Ω' := by
  induction h generalizing u with
  | zero =>
      simp [iterWeakPartial_zero]
  | succ h ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ]
      set f : EuclideanSpace ℝ (Fin d) → ℝ :=
        chosenWeakPartialOrZero (d := d) p (α 0) u Ω with hf_def
      set g : EuclideanSpace ℝ (Fin d) → ℝ :=
        chosenWeakPartialOrZero (d := d) p (α 0) u Ω' with hg_def
      have hf_mem : MemWkp (d := d) h p f Ω := by
        rw [hf_def]
        rw [MemWkp_succ] at hu_mem
        exact hu_mem.2 (α 0)
      have hf_zero : f =ᵐ[volume.restrict U] (fun _ => 0) := by
        rw [hf_def]
        have hu_memW1p : DeGiorgi.MemW1p (d := d) p u Ω := by
          rw [MemWkp_succ] at hu_mem; exact hu_mem.1
        have h_ae_eq : chosenWeakPartialOrZero (d := d) p (α 0) u Ω =ᵐ[volume.restrict U]
            chosenWeakPartialOrZero (d := d) p (α 0) u U :=
          chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hU_open hU_sub hu_memW1p (α 0)
        have h_ae_zero : chosenWeakPartialOrZero (d := d) p (α 0) u U =ᵐ[volume.restrict U]
            (fun _ => 0) :=
          chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp_one hU_open hu_zero (α 0)
        exact h_ae_eq.trans h_ae_zero
      have h_ae_fg : f =ᵐ[volume.restrict Ω'] g := by
        rw [hf_def, hg_def]
        have hu_memW1p : DeGiorgi.MemW1p (d := d) p u Ω := by
          rw [MemWkp_succ] at hu_mem; exact hu_mem.1
        exact chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hΩ' hΩΩ'
          hu_memW1p (α 0)
      have h_ih : iterWeakPartial (d := d) p h (fun i : Fin h => α i.succ) f Ω
          =ᵐ[volume.restrict Ω']
          iterWeakPartial (d := d) p h (fun i : Fin h => α i.succ) f Ω' :=
        ih hf_mem hf_zero (fun i : Fin h => α i.succ)
      have h_congr : iterWeakPartial (d := d) p h (fun i : Fin h => α i.succ) f Ω'
          =ᵐ[volume.restrict Ω']
          iterWeakPartial (d := d) p h (fun i : Fin h => α i.succ) g Ω' :=
        iterWeakPartial_ae_congr (d := d) hp_one hΩ' h
          (fun i : Fin h => α i.succ) h_ae_fg
      exact h_ih.trans h_congr

private lemma iterWeakPartial_ae_eq_tsupport_subset
    {d : ℕ}
    {j : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu_mem : MemWkp (d := d) j p u Ω)
    (hu_support : tsupport u ⊆ Ω')
    (α : Fin j → Fin d) :
    iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict Ω']
      iterWeakPartial (d := d) p j α u Ω' := by
  set U : Set (EuclideanSpace ℝ (Fin d)) := Ω \ tsupport u with hU_def
  have hU_open : IsOpen U := hΩ.sdiff (isClosed_tsupport _)
  have hU_sub : U ⊆ Ω := fun x hx => hx.1
  have hU_contains : Ω \ Ω' ⊆ U := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hx_support
    exact hx.2 (hu_support hx_support)
  have hu_zero : u =ᵐ[volume.restrict U] (fun _ => 0) := by
    refine (ae_restrict_iff' hU_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact image_eq_zero_of_notMem_tsupport hx.2
  exact iterWeakPartial_ae_eq_of_ae_zero_open_subset (d := d) hp_one
    hΩ hΩ' hU_open hΩΩ' hU_sub hU_contains hu_mem hu_zero α

lemma wkpNorm_eq_of_tsupport_subset
    {d : ℕ}
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) k p u Ω) (hu_support : tsupport u ⊆ Ω') :
    MemWkp (d := d) k p u Ω' ∧
    iteratedWeakSobolevNorm (d := d) k p u Ω = iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  have h_mem_Ω' : MemWkp (d := d) k p u Ω' := by
    induction k generalizing u with
    | zero =>
        rw [MemWkp_zero] at hu ⊢
        exact hu.mono_measure (Measure.restrict_mono_set volume hΩΩ')
    | succ k ih =>
        rw [MemWkp_succ] at hu ⊢
        have hu_memW1p : DeGiorgi.MemW1p (d := d) p u Ω := hu.1
        have hu_memW1p_Ω' : DeGiorgi.MemW1p (d := d) p u Ω' :=
          DeGiorgi.MemW1pWitness.restrict (d := d) hΩ' hΩΩ'
            hu_memW1p.someWitness |>.memW1p
        refine ⟨hu_memW1p_Ω', fun i => ?_⟩
        have h_partial_ae :
            chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict Ω']
              chosenWeakPartialOrZero (d := d) p i u Ω' :=
          chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hΩ' hΩΩ'
            hu_memW1p i
        have h_partial_mem_Ω : MemWkp (d := d) k p
            (chosenWeakPartialOrZero (d := d) p i u Ω) Ω := hu.2 i
        have h_partial_mem_Ω' : MemWkp (d := d) k p
            (chosenWeakPartialOrZero (d := d) p i u Ω) Ω' := by
          set f : EuclideanSpace ℝ (Fin d) → ℝ :=
            chosenWeakPartialOrZero (d := d) p i u Ω with hf_def
          have hf_mem : MemWkp (d := d) k p f Ω := h_partial_mem_Ω
          set U : Set (EuclideanSpace ℝ (Fin d)) := Ω \ tsupport u with hU_def
          have hU_open : IsOpen U := hΩ.sdiff (isClosed_tsupport _)
          have hU_sub : U ⊆ Ω := fun x hx => hx.1
          have hf_zero : f =ᵐ[volume.restrict U] (fun _ => 0) := by
            rw [hf_def]
            have hu_U_zero : u =ᵐ[volume.restrict U] (fun _ => 0) := by
              refine (ae_restrict_iff' hU_open.measurableSet).mpr ?_
              refine Filter.Eventually.of_forall ?_
              intro x hx
              exact image_eq_zero_of_notMem_tsupport hx.2
            have hu_memW1p_Ω : DeGiorgi.MemW1p (d := d) p u Ω := hu.1
            have h_ae_eq : chosenWeakPartialOrZero (d := d) p i u Ω =ᵐ[volume.restrict U]
                chosenWeakPartialOrZero (d := d) p i u U :=
              chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hU_open hU_sub hu_memW1p_Ω i
            have h_ae_zero : chosenWeakPartialOrZero (d := d) p i u U =ᵐ[volume.restrict U]
                (fun _ => 0) :=
              chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp_one hU_open hu_U_zero i
            exact h_ae_eq.trans h_ae_zero
          have h_inner : MemWkp (d := d) k p f Ω' :=
            Nat.rec
              (by
                intro g hg_mem _
                rw [MemWkp_zero] at hg_mem ⊢
                exact hg_mem.mono_measure (Measure.restrict_mono_set volume hΩΩ'))
              (fun m ih g hg_mem hg_zero => by
                rw [MemWkp_succ] at hg_mem ⊢
                have hg_memW1p : DeGiorgi.MemW1p (d := d) p g Ω := hg_mem.1
                have hg_memW1p_Ω' : DeGiorgi.MemW1p (d := d) p g Ω' :=
                  DeGiorgi.MemW1pWitness.restrict (d := d) hΩ' hΩΩ'
                    hg_memW1p.someWitness |>.memW1p
                refine ⟨hg_memW1p_Ω', fun i' => ?_⟩
                set g_partial : EuclideanSpace ℝ (Fin d) → ℝ :=
                  chosenWeakPartialOrZero (d := d) p i' g Ω with hg_partial_def
                have hg_partial_mem : MemWkp (d := d) m p g_partial Ω := hg_mem.2 i'
                have hg_partial_zero : g_partial =ᵐ[volume.restrict U] (fun _ => 0) := by
                  rw [hg_partial_def]
                  have h_ae_eq : chosenWeakPartialOrZero (d := d) p i' g Ω =ᵐ[volume.restrict U]
                      chosenWeakPartialOrZero (d := d) p i' g U :=
                    chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hU_open hU_sub
                      hg_memW1p i'
                  have h_ae_zero : chosenWeakPartialOrZero (d := d) p i' g U =ᵐ[volume.restrict U]
                      (fun _ => 0) :=
                    chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp_one hU_open hg_zero i'
                  exact h_ae_eq.trans h_ae_zero
                have h_ih_inner : MemWkp (d := d) m p g_partial Ω' :=
                  ih g_partial hg_partial_mem hg_partial_zero
                rw [hg_partial_def] at h_ih_inner
                have h_ae_eq' : chosenWeakPartialOrZero (d := d) p i' g Ω =ᵐ[volume.restrict Ω']
                    chosenWeakPartialOrZero (d := d) p i' g Ω' :=
                  chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hΩ' hΩΩ'
                    hg_memW1p i'
                exact (MemWkp_congr_ae (d := d) hp_one hΩ' h_ae_eq').mp h_ih_inner)
              k f hf_mem hf_zero
          simpa [hf_def] using h_inner
        exact (MemWkp_congr_ae (d := d) hp_one hΩ' h_partial_ae.symm).mpr h_partial_mem_Ω'
  have h_norm_eq : iteratedWeakSobolevNorm (d := d) k p u Ω = iteratedWeakSobolevNorm (d := d) k p u
    Ω' := by
    unfold iteratedWeakSobolevNorm
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ k := by omega
    have hu_mem_j : MemWkp (d := d) j p u Ω := MemWkp.le_of_le hj_le hu
    refine Finset.sum_congr rfl ?_
    intro α _
    have h_iter_ae : iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict Ω']
        iterWeakPartial (d := d) p j α u Ω' :=
      iterWeakPartial_ae_eq_tsupport_subset (d := d) hp_one hΩ hΩ' hΩΩ'
        hu_mem_j hu_support α
    have h_iter_zero_on_diff :
        iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict (Ω \ Ω')]
          (fun _ => 0) := by
      set U : Set (EuclideanSpace ℝ (Fin d)) := Ω \ tsupport u with hU_def'
      have hU_open' : IsOpen U := hΩ.sdiff (isClosed_tsupport _)
      have hU_sub' : U ⊆ Ω := fun x hx => hx.1
      have hu_zero_U' : u =ᵐ[volume.restrict U] (fun _ => 0) := by
        refine (ae_restrict_iff' hU_open'.measurableSet).mpr ?_
        refine Filter.Eventually.of_forall ?_
        intro x hx
        exact image_eq_zero_of_notMem_tsupport hx.2
      have h_zero_on_U : iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict U]
          (fun _ => 0) :=
        Nat.rec
          (fun α' v hv_mem hzero => by
            simpa [iterWeakPartial_zero] using hzero)
          (fun j' ih α' v hv_mem hzero => by
            rw [iterWeakPartial_succ]
            have hv_memW1p : DeGiorgi.MemW1p (d := d) p v Ω :=
              hv_mem.memW1p
            have h_chosen_zero_U : chosenWeakPartialOrZero (d := d) p (α' 0) v Ω
                =ᵐ[volume.restrict U] (fun _ => 0) := by
              have h_ae_eq : chosenWeakPartialOrZero (d := d) p (α' 0) v Ω =ᵐ[volume.restrict U]
                  chosenWeakPartialOrZero (d := d) p (α' 0) v U :=
                chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hU_open' hU_sub'
                  hv_memW1p (α' 0)
              have h_ae_zero : chosenWeakPartialOrZero (d := d) p (α' 0) v U =ᵐ[volume.restrict U]
                  (fun _ => 0) :=
                chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp_one hU_open' hzero (α' 0)
              exact h_ae_eq.trans h_ae_zero
            have h_partial_mem : MemWkp (d := d) j' p
                (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) Ω :=
              hv_mem.2 (α' 0)
            have h_rest : iterWeakPartial (d := d) p j' (fun i : Fin j' => α' i.succ)
                (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) Ω =ᵐ[volume.restrict U]
                (fun _ => 0) :=
              ih (fun i : Fin j' => α' i.succ)
                (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω)
                h_partial_mem
                h_chosen_zero_U
            simpa using h_rest)
          j α u hu_mem_j hu_zero_U'
      have h_meas_diff : MeasurableSet (Ω \ Ω') :=
        hΩ.measurableSet.diff hΩ'.measurableSet
      have h_diff_subset_U : Ω \ Ω' ⊆ U := by
        intro x hx; refine ⟨hx.1, fun h => hx.2 (hu_support h)⟩
      have h_restrict_eq : (volume.restrict U).restrict (Ω \ Ω') =
          volume.restrict (Ω \ Ω') := by
        rw [Measure.restrict_restrict h_meas_diff]
        rw [Set.inter_eq_left.mpr h_diff_subset_U]
      have h_restricted := h_zero_on_U.restrict (s := Ω \ Ω')
      rw [h_restrict_eq] at h_restricted
      exact h_restricted
    have h_eLp_Ω_eq_Ω' :
        eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω) =
        eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω') :=
      eLpNorm_restrict_eq_of_ae_zero_off
        hΩ.measurableSet hΩ'.measurableSet hΩΩ' h_iter_zero_on_diff
    have h_eLp_eq_on_Ω' :
        eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω') =
        eLpNorm (iterWeakPartial (d := d) p j α u Ω') p (volume.restrict Ω') :=
      eLpNorm_congr_ae h_iter_ae
    rw [h_eLp_Ω_eq_Ω', h_eLp_eq_on_Ω']
  exact ⟨h_mem_Ω', h_norm_eq⟩

private lemma eLpNorm_iterWeakPartial_Ω_le_Ω'_with_U
    {d : ℕ}
    {j : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' U : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hU_open : IsOpen U)
    (hΩΩ' : Ω' ⊆ Ω) (hU_sub : U ⊆ Ω) (_hU_contains : Ω \ Ω' ⊆ U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu_mem : MemWkp (d := d) j p u Ω')
    (hu_zero_U : u =ᵐ[volume.restrict U] (fun _ => 0))
    (α : Fin j → Fin d) :
    eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω') ≤
      eLpNorm (iterWeakPartial (d := d) p j α u Ω') p (volume.restrict Ω') := by
  induction j generalizing u with
  | zero =>
      simp [iterWeakPartial_zero]
  | succ j ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ]
      set f_Ω : EuclideanSpace ℝ (Fin d) → ℝ :=
        chosenWeakPartialOrZero (d := d) p (α 0) u Ω with hf_Ω_def
      set f_Ω' : EuclideanSpace ℝ (Fin d) → ℝ :=
        chosenWeakPartialOrZero (d := d) p (α 0) u Ω' with hf_Ω'_def
      by_cases hu_memW1p_Ω : DeGiorgi.MemW1p (d := d) p u Ω
      · have h_ae_f : f_Ω =ᵐ[volume.restrict Ω'] f_Ω' := by
          rw [hf_Ω_def, hf_Ω'_def]
          exact chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hΩ' hΩΩ'
            hu_memW1p_Ω (α 0)
        have hf_Ω_zero_U : f_Ω =ᵐ[volume.restrict U] (fun _ => 0) := by
          rw [hf_Ω_def]
          have h_ae_eq : chosenWeakPartialOrZero (d := d) p (α 0) u Ω =ᵐ[volume.restrict U]
              chosenWeakPartialOrZero (d := d) p (α 0) u U :=
            chosenWeakPartial_ae_eq_on_subset (d := d) hp_one hΩ hU_open hU_sub hu_memW1p_Ω (α 0)
          have h_ae_zero : chosenWeakPartialOrZero (d := d) p (α 0) u U =ᵐ[volume.restrict U]
              (fun _ => 0) :=
            chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp_one hU_open hu_zero_U (α 0)
          exact h_ae_eq.trans h_ae_zero
        have hf_Ω'_mem : MemWkp (d := d) j p f_Ω' Ω' := by
          rw [hf_Ω'_def]
          rw [MemWkp_succ] at hu_mem
          exact hu_mem.2 (α 0)
        have hf_Ω_mem_Ω' : MemWkp (d := d) j p f_Ω Ω' :=
          (MemWkp_congr_ae (d := d) hp_one hΩ' h_ae_f.symm).mp hf_Ω'_mem
        have h_ih : eLpNorm (iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ) f_Ω Ω)
            p (volume.restrict Ω') ≤
          eLpNorm (iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ) f_Ω Ω')
            p (volume.restrict Ω') :=
          ih hf_Ω_mem_Ω' hf_Ω_zero_U (fun i : Fin j => α i.succ)
        have h_congr : eLpNorm (iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ) f_Ω Ω')
            p (volume.restrict Ω') =
          eLpNorm (iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ) f_Ω' Ω')
            p (volume.restrict Ω') := by
          have h_ae_iter : iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ) f_Ω Ω'
              =ᵐ[volume.restrict Ω']
            iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ) f_Ω' Ω' :=
            iterWeakPartial_ae_congr (d := d) hp_one hΩ' j
              (fun i : Fin j => α i.succ) h_ae_f
          exact eLpNorm_congr_ae h_ae_iter
        rw [h_congr] at h_ih
        exact h_ih
      · rw [hf_Ω_def, chosenWeakPartialOrZero_of_not_mem hu_memW1p_Ω]
        have h_zero_iter : iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
            (0 : EuclideanSpace ℝ (Fin d) → ℝ) Ω =ᵐ[volume.restrict Ω']
            (fun _ => 0) := by
          have h_input_zero : (0 : EuclideanSpace ℝ (Fin d) → ℝ)
              =ᵐ[volume.restrict Ω] (fun _ => 0) := by rfl
          have h := iterWeakPartial_ae_zero_of_input_ae_zero (d := d) hp_one hΩ
            j (fun i : Fin j => α i.succ) h_input_zero
          have h_meas : MeasurableSet Ω' := hΩ'.measurableSet
          have h_restrict_eq : (volume.restrict Ω).restrict Ω' = volume.restrict Ω' := by
            rw [Measure.restrict_restrict h_meas, Set.inter_eq_left.mpr hΩΩ']
          have h_restricted := h.restrict (s := Ω')
          simpa [h_restrict_eq] using h_restricted
        rw [eLpNorm_congr_ae h_zero_iter]
        simp

lemma wkpNorm_le_of_tsupport_subset_mem_small
    {d : ℕ}
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) k p u Ω') (hu_support : tsupport u ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p u Ω ≤ iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  have hu_zero_diff : ∀ x ∈ Ω \ Ω', u x = 0 := by
    intro x hx
    have hx_off : x ∉ tsupport u := fun h => hx.2 (hu_support h)
    exact image_eq_zero_of_notMem_tsupport hx_off
  have h_meas_diff : MeasurableSet (Ω \ Ω') :=
    hΩ.measurableSet.diff hΩ'.measurableSet
  have hu_zero_diff_ae : ∀ᵐ x ∂(volume.restrict (Ω \ Ω')), u x = 0 := by
    refine (ae_restrict_iff' h_meas_diff).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact hu_zero_diff x hx
  set U : Set (EuclideanSpace ℝ (Fin d)) := Ω \ tsupport u with hU_def
  have hU_open : IsOpen U := hΩ.sdiff (isClosed_tsupport _)
  have hU_sub : U ⊆ Ω := fun x hx => hx.1
  have h_diff_sub_U : Ω \ Ω' ⊆ U := by
    intro x hx
    refine ⟨hx.1, fun h => hx.2 (hu_support h)⟩
  have hu_zero_U : u =ᵐ[volume.restrict U] (fun _ => 0) := by
    refine (ae_restrict_iff' hU_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact image_eq_zero_of_notMem_tsupport hx.2
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_le_sum ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hj_le : j ≤ k := by omega
  have hu_mem_j : MemWkp (d := d) j p u Ω' := MemWkp.le_of_le hj_le hu
  refine Finset.sum_le_sum ?_
  intro α _
  have h_iter_zero_on_diff :
      iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict (Ω \ Ω')]
        (fun _ => 0) := by
    have h_zero_on_U : iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict U]
        (fun _ => 0) :=
      Nat.rec
        (fun α' v hv_zero => by
          simpa [iterWeakPartial_zero] using hv_zero)
        (fun j' ih α' v hv_zero => by
          rw [iterWeakPartial_succ]
          by_cases hv_memW1p_Ω : DeGiorgi.MemW1p (d := d) p v Ω
          · have hP_Ω : DeGiorgi.HasWeakPartialDeriv (d := d) (α' 0)
                (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) v Ω :=
              chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hv_memW1p_Ω (α' 0)
            have hP_U : DeGiorgi.HasWeakPartialDeriv (d := d) (α' 0)
                (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) v U :=
              DeGiorgi.HasWeakPartialDeriv.restrict (d := d) hU_open hU_sub hP_Ω
            have hZero_isWeak : DeGiorgi.HasWeakPartialDeriv (d := d) (α' 0)
                (fun _ => (0 : ℝ)) v U := by
              intro φ hφ hφ_support hφ_sub
              have h_integrand_zero : (fun x => v x * (fderiv ℝ φ x)
                (EuclideanSpace.single (α' 0) 1))
                  =ᵐ[volume.restrict U] (fun _ => (0 : ℝ)) := by
                filter_upwards [hv_zero] with x hx
                simp [hx]
              have hint_lhs : ∫ x in U, v x * (fderiv ℝ φ x) (EuclideanSpace.single (α' 0) 1) = 0 :=
                integral_eq_zero_of_ae h_integrand_zero
              rw [hint_lhs]; simp
            have hP_local_U : LocallyIntegrable
                (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) (volume.restrict U) := by
              have hmem : MeasureTheory.MemLp
                  (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) p (volume.restrict Ω) :=
                chosenWeakPartialOrZero_memLp_of_mem (d := d) hv_memW1p_Ω (α' 0)
              have hmem' : MeasureTheory.MemLp
                  (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) p (volume.restrict U) :=
                hmem.mono_measure (Measure.restrict_mono_set volume hU_sub)
              exact hmem'.locallyIntegrable hp_one
            have hZero_local_U : LocallyIntegrable
                (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (volume.restrict U) :=
              locallyIntegrable_const (0 : ℝ)
            have h_chosen_zero_U : chosenWeakPartialOrZero (d := d) p (α' 0) v Ω
                =ᵐ[volume.restrict U] (fun _ => (0 : ℝ)) :=
              DeGiorgi.HasWeakPartialDeriv.ae_eq hU_open hP_U hZero_isWeak hP_local_U hZero_local_U
            exact ih (fun i : Fin j' => α' i.succ)
              (chosenWeakPartialOrZero (d := d) p (α' 0) v Ω) h_chosen_zero_U
          · rw [chosenWeakPartialOrZero_of_not_mem hv_memW1p_Ω]
            have h0 : (0 : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] (fun _ => 0) :=
              by rfl
            have htemp := iterWeakPartial_ae_zero_of_input_ae_zero (d := d) hp_one hΩ
              j' (fun i : Fin j' => α' i.succ) h0
            have hUmeas : MeasurableSet U := hU_open.measurableSet
            have hrestr : (volume.restrict Ω).restrict U = volume.restrict U := by
              rw [Measure.restrict_restrict hUmeas, Set.inter_eq_left.mpr hU_sub]
            have htemp_restricted := htemp.restrict (s := U)
            simpa [hrestr] using htemp_restricted)
        j α u hu_zero_U
    have h_restrict_eq : (volume.restrict U).restrict (Ω \ Ω') =
        volume.restrict (Ω \ Ω') := by
      rw [Measure.restrict_restrict h_meas_diff]
      rw [Set.inter_eq_left.mpr h_diff_sub_U]
    have h_restricted := h_zero_on_U.restrict (s := Ω \ Ω')
    rw [h_restrict_eq] at h_restricted
    exact h_restricted
  have h_eLp_Ω_eq_Ω' :
      eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω') :=
    eLpNorm_restrict_eq_of_ae_zero_off
      hΩ.measurableSet hΩ'.measurableSet hΩΩ' h_iter_zero_on_diff
  rw [h_eLp_Ω_eq_Ω']
  exact eLpNorm_iterWeakPartial_Ω_le_Ω'_with_U (d := d) hp_one hΩ hΩ' hU_open hΩΩ' hU_sub
    h_diff_sub_U hu_mem_j hu_zero_U α

end Euclidean

namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem cross_chart_bound_strict_strong_memWkp
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ},
        Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 p v
            (chartTargetEuclid (I := I) (M := M) α) →
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α →
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I α v))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
        ENNReal.ofReal K *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p v
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set K_M : Set M := K_α ∩ tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKM_def
  have hKM_compact : IsCompact K_M :=
    hK_compact.inter_right (isClosed_tsupport _)
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx => hK_α_in_α hx.1
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M γ hx.2
  by_cases hKM_empty : K_M = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro v _hv_mem hv_support
    have h_pushed_zero := chartPushed_chartPullback_zero_of_K_M_empty
      (I := I) (M := M) γ α hK_α_in_α hKM_empty hv_support
    rw [h_pushed_zero]
    rw [Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) γ)]
    exact zero_le
  obtain ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
    hΩγα_subset_overlap, _hΩαγ_subset_overlap, hKM_image_in_Ωγα, Φ,
    hΦ_eq_on_Ωγα, _hΦ_inv_eq_on_Ωαγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      γ α hKM_compact hKM_in_γ hKM_in_α 1
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M
    with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M
    with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEα_compact : IsCompact K_E_α :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKM_compact hKM_in_α
  have hKEγ_subset_target : K_E_γ ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  have hKEα_subset_target : K_E_α ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H α).source := hKM_in_α hxK
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I α x, h_target, rfl⟩
  have hΦ_eq_KM : ∀ x ∈ K_M, Φ.toFun ((toEuclidean (E := E)) (extChartAt I γ x)) =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    intro x hxK
    set y := (toEuclidean (E := E)) (extChartAt I γ x) with hy_def
    have hy_in_KEγ : y ∈ K_E_γ := ⟨x, hxK, rfl⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy_in_KEγ
    have h1 : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
      hΦ_eq_on_Ωγα y hy_in_Ωγα
    rw [h1]
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    rw [hy_def]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_chart
  have hKEα_eq_Φ_image : K_E_α = Φ.toFun '' K_E_γ := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hxK, hxz⟩
      refine ⟨(toEuclidean (E := E)) (extChartAt I γ x), ?_, ?_⟩
      · exact ⟨x, hxK, rfl⟩
      · have := hΦ_eq_KM x hxK
        rw [this]; exact hxz
    · rintro ⟨y, hy, hyz⟩
      rcases hy with ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      have := hΦ_eq_KM x hxK
      rw [← hyz, ← hxy, this]
  have hKEα_in_Ωαγ : K_E_α ⊆ Ω_αγ := by
    rw [hKEα_eq_Φ_image]
    intro z hz
    rcases hz with ⟨y, hy, hyz⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy
    rw [← hyz]; exact Φ.bijOn.mapsTo hy_in_Ωγα
  set Uγ : Set EuclN := Ω_γα ∩ chartTargetEuclid (I := I) (M := M) γ with hUγ_def
  have hUγ_open : IsOpen Uγ :=
    hΩγα_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) γ)
  have hKEγ_in_Uγ : K_E_γ ⊆ Uγ :=
    Set.subset_inter hKM_image_in_Ωγα hKEγ_subset_target
  obtain ⟨δ_γ, η_γ_local, _hδ_γ_pos, _hδγ_subset, hη_γ_local_smooth, hη_γ_local_compact,
    hη_γ_local_range, hη_γ_local_one, hη_γ_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEγ_compact hUγ_open hKEγ_in_Uγ
  have hη_γ_local_support_Ωγα : tsupport η_γ_local ⊆ Ω_γα :=
    fun y hy => (hη_γ_local_support hy).1
  have hη_γ_local_support_target : tsupport η_γ_local ⊆ chartTargetEuclid (I := I) (M := M) γ :=
    fun y hy => (hη_γ_local_support hy).2
  set Uα : Set EuclN := Ω_αγ ∩ chartTargetEuclid (I := I) (M := M) α with hUα_def
  have hUα_open : IsOpen Uα :=
    hΩαγ_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) α)
  have hKEα_in_Uα : K_E_α ⊆ Uα :=
    Set.subset_inter hKEα_in_Ωαγ hKEα_subset_target
  obtain ⟨_δ_α, η_α_local, _hδ_α_pos, _hδα_subset, hη_α_local_smooth, hη_α_local_compact,
    hη_α_local_range, hη_α_local_one, hη_α_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEα_compact hUα_open hKEα_in_Uα
  have hη_α_local_support_Ωαγ : tsupport η_α_local ⊆ Ω_αγ :=
    fun y hy => (hη_α_local_support hy).1
  have hη_α_local_support_target : tsupport η_α_local ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hη_α_local_support hy).2
  set ρ_γ_M : M → ℝ :=
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_γ_M_def
  have hρ_γ_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ρ_γ_M :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hρ_γ_M_support_in_chart : tsupport ρ_γ_M ⊆ (chartAt H γ).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M γ
  have hρ_γ_M_compact : HasCompactSupport ρ_γ_M :=
    (isClosed_tsupport _).isCompact
  have hρ_γ_M_range : Set.range ρ_γ_M ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro v ⟨x, hx⟩
    rw [← hx]
    refine ⟨?_, ?_⟩
    · exact (CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg γ x
    · exact (CalabiYau.RiemannianVolume.chartAtlasPOU I M).le_one γ x
  set ργE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) γ ρ_γ_M with hργE_def
  have hργE_smooth : ContDiff ℝ (⊤ : ℕ∞) ργE :=
    contDiff_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth hρ_γ_M_compact
      hρ_γ_M_support_in_chart
  have hργE_range : Set.range ργE ⊆ Set.Icc (0 : ℝ) 1 :=
    etaEuclid_range_Icc (I := I) (M := M) γ ρ_γ_M hρ_γ_M_range
  have hργE_norm_one : ∀ y : EuclN, ‖ργE y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hργE_range
  obtain ⟨C_ργE_grad, _hC_ργE_pos, hC_ργE_grad⟩ :=
    exists_grad_bound_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth
      hρ_γ_M_compact hρ_γ_M_support_in_chart
  have hη_γ_local_norm_one : ∀ y : EuclN, ‖η_γ_local y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_γ_local_range
  obtain ⟨C_η_γ_grad, _hC_η_γ_pos, hC_η_γ_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_γ_local_smooth hη_γ_local_compact
  have hη_α_local_norm_one : ∀ y : EuclN, ‖η_α_local y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_α_local_range
  obtain ⟨C_η_α_grad, _hC_η_α_pos, hC_η_α_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_α_local_smooth hη_α_local_compact
  set η_combined : EuclN → ℝ := fun y => η_γ_local y * ργE y with hη_combined_def
  have hη_combined_smooth : ContDiff ℝ (⊤ : ℕ∞) η_combined :=
    hη_γ_local_smooth.mul hργE_smooth
  have hη_combined_bound : ∀ y : EuclN, ‖η_combined y‖ ≤ 1 := by
    intro y
    have h := mul_le_mul (a := ‖η_γ_local y‖) (b := 1) (c := ‖ργE y‖) (d := 1)
      (hη_γ_local_norm_one y) (hργE_norm_one y) (norm_nonneg _) zero_le_one
    rw [show η_combined y = η_γ_local y * ργE y from rfl, norm_mul, mul_one] at *
    exact h
  set C_combined_grad : ℝ := C_η_γ_grad + C_ργE_grad with hC_combined_grad_def
  have hC_combined_grad_bound : ∀ y : EuclN, ‖fderiv ℝ η_combined y‖ ≤ C_combined_grad := by
    intro y
    have h_eq :
        η_combined = fun y => η_γ_local y * ργE y := rfl
    have hη_γ_local_diff : DifferentiableAt ℝ η_γ_local y :=
      (hη_γ_local_smooth.differentiable (by simp)).differentiableAt
    have hργE_diff : DifferentiableAt ℝ ργE y :=
      (hργE_smooth.differentiable (by simp)).differentiableAt
    rw [h_eq]
    rw [fderiv_fun_mul hη_γ_local_diff hργE_diff]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖η_γ_local y • fderiv ℝ ργE y‖ ≤ C_ργE_grad := by
      rw [norm_smul]
      have : ‖η_γ_local y‖ * ‖fderiv ℝ ργE y‖ ≤ 1 * C_ργE_grad :=
        mul_le_mul (hη_γ_local_norm_one y) (hC_ργE_grad y) (norm_nonneg _) zero_le_one
      simpa using this
    have h2 : ‖ργE y • fderiv ℝ η_γ_local y‖ ≤ C_η_γ_grad := by
      rw [norm_smul]
      have : ‖ργE y‖ * ‖fderiv ℝ η_γ_local y‖ ≤ 1 * C_η_γ_grad :=
        mul_le_mul (hργE_norm_one y) (hC_η_γ_grad y) (norm_nonneg _) zero_le_one
      simpa using this
    linarith [h1, h2]
  set Cmax_combined : ℝ := max 1 C_combined_grad with hCmax_combined_def
  have hCmax_combined_norm : ∀ y : EuclN, ‖η_combined y‖ ≤ Cmax_combined :=
    fun y => (hη_combined_bound y).trans (le_max_left _ _)
  have hCmax_combined_grad : ∀ y : EuclN, ‖fderiv ℝ η_combined y‖ ≤ Cmax_combined :=
    fun y => (hC_combined_grad_bound y).trans (le_max_right _ _)
  set Cmax_η_α : ℝ := max 1 C_η_α_grad with hCmax_η_α_def
  have hCmax_η_α_norm : ∀ y : EuclN, ‖η_α_local y‖ ≤ Cmax_η_α :=
    fun y => (hη_α_local_norm_one y).trans (le_max_left _ _)
  have hCmax_η_α_grad : ∀ y : EuclN, ‖fderiv ℝ η_α_local y‖ ≤ Cmax_η_α :=
    fun y => (hC_η_α_grad y).trans (le_max_right _ _)
  set Ωγ_target : Set EuclN := chartTargetEuclid (I := I) (M := M) γ with hΩγ_target_def
  set Ωα_target : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩα_target_def
  have hΩγ_target_open : IsOpen Ωγ_target := chartTargetEuclid_isOpen (I := I) (M := M) γ
  have hΩα_target_open : IsOpen Ωα_target := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hCmax_combined_nonneg : 0 ≤ Cmax_combined :=
    le_trans zero_le_one (le_max_left _ _)
  have hη_combined_iter_bound :
      ∀ j ≤ 1, ∀ y ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined y‖ ≤ Cmax_combined := by
    intro j hj y _
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact hCmax_combined_norm y
    · rw [norm_iteratedFDeriv_one]; exact hCmax_combined_grad y
  obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
    Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      1 (le_refl _) (d := Module.finrank ℝ E) hp_one hp_top hΩγα_open hη_combined_smooth
      hCmax_combined_nonneg hη_combined_iter_bound
  have hCmax_η_α_nonneg : 0 ≤ Cmax_η_α :=
    le_trans zero_le_one (le_max_left _ _)
  have hη_α_local_iter_bound :
      ∀ j ≤ 1, ∀ y ∈ Ωα_target, ‖iteratedFDeriv ℝ j η_α_local y‖ ≤ Cmax_η_α := by
    intro j hj y _
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact hCmax_η_α_norm y
    · rw [norm_iteratedFDeriv_one]; exact hCmax_η_α_grad y
  obtain ⟨K_leib_α, hK_leib_α_pos, hK_leib_α_bound⟩ :=
    Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      1 (le_refl _) (d := Module.finrank ℝ E) hp_one hp_top hΩα_target_open hη_α_local_smooth
      hCmax_η_α_nonneg hη_α_local_iter_bound
  set K_chain : ℝ := Φ.wkpCompositionConstant 1 p with hK_chain_def
  have hK_chain_pos : 0 < K_chain := by
    have hp_zero : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one
      exact absurd hp_one (by norm_num)
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
    have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
    have hjLB_inv_pos : 0 < 1 / Φ.jacobianLowerBound := by positivity
    have hKchg_pos : 0 < (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) :=
      Real.rpow_pos_of_pos hjLB_inv_pos _
    rw [hK_chain_def]
    unfold Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpCompositionConstant
    have h_zero_in : (0 : ℕ) ∈ Finset.range (1 + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_card_pos : 0 < (Finset.range (1 + 1)).sum
        (fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ)) := by
      have h_le := Finset.single_le_sum (s := Finset.range (1 + 1))
        (f := fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ))
        (fun j _ => by positivity) h_zero_in
      rw [h_at_zero] at h_le
      linarith
    have h_kfact_D_pos : 0 < ((1 : ℕ).factorial : ℝ) * Φ.derivBoundMaxOne ^ 1 := by
      refine mul_pos ?_ ?_
      · exact_mod_cast Nat.factorial_pos 1
      · exact pow_pos Φ.derivBoundMaxOne_pos 1
    have h_k1_pos : (0 : ℝ) < ((1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ 1
    positivity
  set K : ℝ := K_leib * K_chain * K_leib_α with hK_def
  have hK_pos : 0 < K := mul_pos (mul_pos hK_leib_pos hK_chain_pos) hK_leib_α_pos
  refine ⟨K, hK_pos, ?_⟩
  intro v hv_mem hv_support
  set χ_local : EuclN → ℝ := fun y => η_α_local y * v y with hχ_local_def
  have hχ_local_support_in_η_α : tsupport χ_local ⊆ tsupport η_α_local := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_α_local y ≠ 0 := by
      intro h0
      apply hy
      change η_α_local y * v y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hχ_local_support_in_Ωαγ : tsupport χ_local ⊆ Ω_αγ :=
    hχ_local_support_in_η_α.trans hη_α_local_support_Ωαγ
  have hχ_local_support_in_Ωα_target : tsupport χ_local ⊆ Ωα_target :=
    hχ_local_support_in_η_α.trans hη_α_local_support_target
  have hχ_local_compact : HasCompactSupport χ_local :=
    hη_α_local_compact.of_isClosed_subset (isClosed_tsupport _) hχ_local_support_in_η_α
  have hχ_local_mem_Ωα_target : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p χ_local Ωα_target := by
    have h_bound : ∀ j ≤ 1, ∀ x ∈ Ωα_target, ‖iteratedFDeriv ℝ j η_α_local x‖ ≤ Cmax_η_α := by
      intro j hj x _
      interval_cases j
      · rw [norm_iteratedFDeriv_zero]; exact hCmax_η_α_norm x
      · rw [norm_iteratedFDeriv_one]; exact hCmax_η_α_grad x
    exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) 1 hp_one hΩα_target_open hη_α_local_smooth h_bound hv_mem
  have hχ_local_pair_target_Ωαγ :=
    Sobolev.Euclidean.wkpNorm_eq_of_tsupport_subset_one
      (d := Module.finrank ℝ E) hp_one hΩα_target_open hΩαγ_open
      hΩαγ_subset_target hχ_local_mem_Ωα_target hχ_local_support_in_Ωαγ
  have hχ_local_mem_Ωαγ : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p χ_local Ω_αγ := hχ_local_pair_target_Ωαγ.1
  have hχ_local_norm_target_eq_Ωαγ :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_local Ωα_target =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p χ_local Ω_αγ := hχ_local_pair_target_Ωαγ.2
  set ψ_total : EuclN → ℝ := fun y => η_combined y * χ_local (Φ.toFun y) with hψ_total_def
  have hψ_total_support_in_η_combined : tsupport ψ_total ⊆ tsupport η_combined := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_combined y ≠ 0 := by
      intro h0
      apply hy
      change η_combined y * χ_local (Φ.toFun y) = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hη_combined_support_in_η_γ : tsupport η_combined ⊆ tsupport η_γ_local := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_γ_ne : η_γ_local y ≠ 0 := by
      intro h0
      apply hy
      change η_γ_local y * ργE y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_γ_ne
  have hψ_total_support_in_Ωγα : tsupport ψ_total ⊆ Ω_γα :=
    (hψ_total_support_in_η_combined.trans hη_combined_support_in_η_γ).trans hη_γ_local_support_Ωγα
  have h_pointwise_eq : ∀ y ∈ Ωγ_target,
      chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (chartPullback I α v) y = ψ_total y := by
    intro y hy_target
    set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
      have := hy_target
      rw [hΩγ_target_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at this
      exact this
    have hz_source : z ∈ (extChartAt I γ).source :=
      (extChartAt I γ).map_target hsymm_target
    have hz_chartγ : z ∈ (chartAt H γ).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hz_source
      exact hz_source
    have h_pushed_eq : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v) y =
        ρ_γ_M z * chartPullback I α v z := by
      unfold chartPushed
      rfl
    rw [h_pushed_eq]
    have hργE_y : ργE y = ρ_γ_M z := by
      rw [hργE_def]
      exact etaEuclid_apply_of_mem (I := I) (M := M) γ ρ_γ_M hy_target
    have hψ_total_y : ψ_total y = η_γ_local y * ργE y * χ_local (Φ.toFun y) := rfl
    rw [hψ_total_y]
    by_cases h_y_in_support_η_γ : y ∈ tsupport η_γ_local
    · have hy_in_Ωγα : y ∈ Ω_γα := hη_γ_local_support_Ωγα h_y_in_support_η_γ
      by_cases hρ_zero : ρ_γ_M z = 0
      · rw [hρ_zero, hργE_y, hρ_zero]; ring
      · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
          have h_in : z ∈ Function.support ρ_γ_M := by
            simp only [Function.mem_support, ne_eq]; exact hρ_zero
          exact subset_tsupport _ h_in
        by_cases hz_in_α : z ∈ (chartAt H α).source
        · rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_in_α]
          by_cases hz_in_Kα : z ∈ K_α
          · have hz_in_KM : z ∈ K_M := ⟨hz_in_Kα, hz_in_tsupp_ρ⟩
            have hy_in_KEγ : y ∈ K_E_γ := by
              refine ⟨z, hz_in_KM, ?_⟩
              change (toEuclidean (E := E)) (extChartAt I γ z) = y
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              rw [h_z_chart]
              exact (toEuclidean (E := E)).apply_symm_apply y
            have hη_γ_local_y : η_γ_local y = 1 := by
              apply hη_γ_local_one
              exact Metric.self_subset_cthickening K_E_γ hy_in_KEγ
            have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
              have h := hΦ_eq_KM z hz_in_KM
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
                rw [h_z_chart]
                exact (toEuclidean (E := E)).apply_symm_apply y
              rw [← hy_eq]
              exact h
            rw [hΦ_y]
            have h_Φy_in_KEα : (toEuclidean (E := E)) (extChartAt I α z) ∈ K_E_α :=
              ⟨z, hz_in_KM, rfl⟩
            have hη_α_local_Φy : η_α_local ((toEuclidean (E := E)) (extChartAt I α z)) = 1 := by
              apply hη_α_local_one
              exact Metric.self_subset_cthickening K_E_α h_Φy_in_KEα
            have hχ_local_Φy : χ_local ((toEuclidean (E := E)) (extChartAt I α z)) =
                v ((toEuclidean (E := E)) (extChartAt I α z)) := by
              change η_α_local _ * v _ = v _
              rw [hη_α_local_Φy]; ring
            rw [hχ_local_Φy, hη_γ_local_y, hργE_y]
            ring
          · have hvα_z_eq : (toEuclidean (E := E)) (extChartAt I α z) ∉ tsupport v := by
              intro hin
              have := hv_support hin
              rcases this with ⟨x', hx'_K, hx'_eq⟩
              have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K
              have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
                have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                    (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
                exact (toEuclidean (E := E)).injective h_eu
              have hz_in_α_ext : z ∈ (extChartAt I α).source := by
                rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
                  (I := I) (M := M)]
                exact hz_in_α
              have hx'_α_ext : x' ∈ (extChartAt I α).source := by
                rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
                  (I := I) (M := M)]
                exact hx'_chart
              have h_inj := (extChartAt I α).injOn hx'_α_ext hz_in_α_ext h_eq_chart_α
              have : z ∈ K_α := by rw [← h_inj]; exact hx'_K
              exact hz_in_Kα this
            have hv_z : v ((toEuclidean (E := E)) (extChartAt I α z)) = 0 :=
              image_eq_zero_of_notMem_tsupport hvα_z_eq
            have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
              rw [hΦ_eq_on_Ωγα y hy_in_Ωγα]
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
                rw [h_z_chart]
                exact (toEuclidean (E := E)).apply_symm_apply y
              rw [← hy_eq]
              exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hz_chartγ
            have hχ_local_zero : χ_local ((toEuclidean (E := E)) (extChartAt I α z)) = 0 := by
              change η_α_local _ * v _ = 0
              rw [hv_z]; ring
            rw [hΦ_y, hχ_local_zero, hv_z]; ring
        · rw [chartPullback_apply_of_notMem (I := I) (M := M) α v hz_in_α]
          exfalso
          have hy_in_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
            hΩγα_subset_overlap hy_in_Ωγα
          unfold chartOverlapEuclid at hy_in_overlap
          rcases hy_in_overlap with ⟨z', ⟨w, hw_inter, hwz'⟩, hz'y⟩
          have hy_eq : (toEuclidean (E := E)) (extChartAt I γ w) = y := by
            rw [← hz'y, ← hwz']
          have h_w_chart_γ : w ∈ (extChartAt I γ).source := by
            rw [extChartAt_source]; exact hw_inter.1
          have h_z_eq_w : z = w := by
            have h_y_eq_chart : (toEuclidean (E := E)).symm y = extChartAt I γ w := by
              rw [← hy_eq, (toEuclidean (E := E)).symm_apply_apply]
            change (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = w
            rw [h_y_eq_chart]
            exact (extChartAt I γ).left_inv h_w_chart_γ
          rw [h_z_eq_w] at hz_in_α
          exact hz_in_α hw_inter.2
    · have h_zero : η_γ_local y = 0 := image_eq_zero_of_notMem_tsupport h_y_in_support_η_γ
      rw [h_zero]; simp only [zero_mul]
      by_cases hρ_zero : ρ_γ_M z = 0
      · rw [hρ_zero]; ring
      · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
          have h_in : z ∈ Function.support ρ_γ_M := by
            simp only [Function.mem_support, ne_eq]; exact hρ_zero
          exact subset_tsupport _ h_in
        by_cases hpb_zero : chartPullback I α v z = 0
        · rw [hpb_zero]; ring
        · exfalso
          have hz_chartα : z ∈ (chartAt H α).source := by
            by_contra hcontra
            apply hpb_zero
            exact chartPullback_apply_of_notMem (I := I) (M := M) α v hcontra
          rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_chartα] at hpb_zero
          have h_arg_in_tsupp_v : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport v := by
            have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support v := by
              simp only [Function.mem_support, ne_eq]; exact hpb_zero
            exact subset_tsupport _ this
          have h_arg_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
              (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
            hv_support h_arg_in_tsupp_v
          obtain ⟨x', hx'_K_α, hx'_eq⟩ := h_arg_in_image_K_α
          have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K_α
          have h_eq_chart : extChartAt I α x' = extChartAt I α z := by
            have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
            exact (toEuclidean (E := E)).injective h_eu
          have hx'_α_ext : x' ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hx'_chart
          have hz_α_ext : z ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hz_chartα
          have h_inj := (extChartAt I α).injOn hx'_α_ext hz_α_ext h_eq_chart
          have hz_in_K_α : z ∈ K_α := by rw [← h_inj]; exact hx'_K_α
          have hz_in_K_M : z ∈ K_M := ⟨hz_in_K_α, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := by
            refine ⟨z, hz_in_K_M, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I γ z) = y
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          have hy_in_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
            Metric.self_subset_cthickening K_E_γ hy_in_KEγ
          have h_η_y_one : η_γ_local y = 1 := hη_γ_local_one y hy_in_cthick
          have hy_in_support : y ∈ Function.support η_γ_local := by
            simp only [Function.mem_support, ne_eq, h_η_y_one]
            exact one_ne_zero
          exact h_y_in_support_η_γ (subset_tsupport _ hy_in_support)
  have h_ae_eq : (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v)) =ᵐ[volume.restrict Ωγ_target] ψ_total := by
    refine (ae_restrict_iff' hΩγ_target_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact h_pointwise_eq y hy
  rw [Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩγ_target_open h_ae_eq]
  have h_χ_local_comp_mem :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p (fun y => χ_local (Φ.toFun y)) Ω_γα :=
    Sobolev.Euclidean.MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := Module.finrank ℝ E) 1 (le_refl 1) hp_one hp_top hΩγα_open hΩαγ_open Φ
      hχ_local_mem_Ωαγ hχ_local_compact hχ_local_support_in_Ωαγ
  have hψ_total_mem_Ωγα :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα := by
    have h_bound : ∀ j ≤ 1, ∀ x ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined x‖ ≤ Cmax_combined := by
      intro j hj x _
      interval_cases j
      · rw [norm_iteratedFDeriv_zero]; exact hCmax_combined_norm x
      · rw [norm_iteratedFDeriv_one]; exact hCmax_combined_grad x
    exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) 1 hp_one hΩγα_open hη_combined_smooth h_bound
      h_χ_local_comp_mem
  have h_bridge_γ :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ωγ_target ≤
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα :=
    Sobolev.Euclidean.wkpNorm_le_of_tsupport_subset_mem_small_one
      (d := Module.finrank ℝ E) hp_one hΩγ_target_open hΩγα_open
      hΩγα_subset_target hψ_total_mem_Ωγα hψ_total_support_in_Ωγα
  refine h_bridge_γ.trans ?_
  have h_leib_step : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p ψ_total Ω_γα ≤
      ENNReal.ofReal K_leib *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => χ_local (Φ.toFun y)) Ω_γα :=
    hK_leib_bound h_χ_local_comp_mem
  refine h_leib_step.trans ?_
  have h_chain_step :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => χ_local (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p χ_local Ω_αγ :=
    Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le
      hp_one hp_top hΩγα_open hΩαγ_open Φ 1 (le_refl 1)
      hχ_local_mem_Ωαγ hχ_local_compact hχ_local_support_in_Ωαγ
  have h_chain_step_target :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => χ_local (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p χ_local Ωα_target := by
    refine h_chain_step.trans ?_
    rw [hχ_local_norm_target_eq_Ωαγ]
  have h_leib_α_step : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p χ_local Ωα_target ≤
      ENNReal.ofReal K_leib_α *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p v Ωα_target := by
    have h_eq : χ_local = (fun y => η_α_local y * v y) := rfl
    rw [h_eq]
    exact hK_leib_α_bound hv_mem
  have h_chain_combined : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p (fun y => χ_local (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        (ENNReal.ofReal K_leib_α *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p v Ωα_target) := by
    refine h_chain_step_target.trans ?_
    exact mul_le_mul_of_nonneg_left h_leib_α_step (zero_le)
  refine (mul_le_mul_of_nonneg_left h_chain_combined (zero_le)).trans ?_
  have h_K_eq : ENNReal.ofReal K_leib *
      (ENNReal.ofReal K_chain * (ENNReal.ofReal K_leib_α *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p v Ωα_target)) =
      ENNReal.ofReal K *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p v Ωα_target := by
    rw [hK_def]
    rw [ENNReal.ofReal_mul (mul_pos hK_leib_pos hK_chain_pos).le]
    rw [ENNReal.ofReal_mul hK_leib_pos.le]
    ring
  exact h_K_eq ▸ le_refl _

end Chart

end Sobolev
