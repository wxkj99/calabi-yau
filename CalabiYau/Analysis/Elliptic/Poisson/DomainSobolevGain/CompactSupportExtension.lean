module

public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import CalabiYau.Analysis.Sobolev.Euclidean.Density
import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

/-!
# Extending local Sobolev membership past a compact support

A function in `W^{k,2}(Ω')` that vanishes a.e. on `Ω \ K`, with `K ⊆ Ω' ⊆ Ω` and `K`
compact, is in `W^{k,2}(Ω)`.

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/Bootstrap/ChartHm.lean`,
`MemWkp.extend_of_ae_zero_outside_compact` (lines 50–183): multiply by a smooth cutoff
equal to one near `K` and supported in `Ω'`, then extend by zero
(`MemWkp.extend_zero`, `Sobolev/Euclidean/Density.lean`).
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CalabiYau.PoissonDomainRegularity

/-- Local `W^{k,2}` on a neighborhood of a compact support extends to the larger open set. -/
theorem memWkp_extend_of_ae_zero_outside_compact
    {d : ℕ} (k : ℕ) {Ω Ω' K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω') (hΩ'_in_Ω : Ω' ⊆ Ω)
    (hK_compact : IsCompact K) (hK_in_Ω' : K ⊆ Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu_local : Sobolev.Euclidean.MemWkp (d := d) k 2 u Ω')
    (hu_ae_zero : ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)),
      u y = 0) :
    Sobolev.Euclidean.MemWkp (d := d) k 2 u Ω := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_in_Ω', hη_smooth, hη_compact_support, hη_range,
    hη_one_on_cthick, hη_tsupp_in_Ω'⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := d) hK_compact hΩ'_open hK_in_Ω'
  obtain ⟨C, hC_nn, hη_bound⟩ :=
    Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) hη_smooth hη_compact_support k
  have h_eta_u_in_Ω' : Sobolev.Euclidean.MemWkp
      (d := d) k 2 (fun x => η x * u x) Ω' :=
    Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := d) k (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'_open hη_smooth
      (fun j _hj x _hx => hη_bound x j _hj) hu_local
  have h_tsupp_prod_in_tsupp_eta : tsupport (fun x => η x * u x) ⊆ tsupport η := by
    refine closure_mono ?_
    intro x hx
    have hx_ne : η x * u x ≠ 0 := hx
    intro hx_eta_zero
    apply hx_ne
    rw [hx_eta_zero]
    ring
  have h_tsupp_prod_in_Ω' : tsupport (fun x => η x * u x) ⊆ Ω' :=
    h_tsupp_prod_in_tsupp_eta.trans hη_tsupp_in_Ω'
  have h_compactSupport_prod : HasCompactSupport (fun x => η x * u x) :=
    hη_compact_support.of_isClosed_subset (isClosed_tsupport _)
      h_tsupp_prod_in_tsupp_eta
  have h_eta_u_in_Ω : Sobolev.Euclidean.MemWkp
      (d := d) k 2 (fun x => η x * u x) Ω :=
    Sobolev.Euclidean.MemWkp.extend_zero
      (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hΩ'_open hΩ_open hΩ'_in_Ω h_eta_u_in_Ω' h_tsupp_prod_in_Ω'
      h_compactSupport_prod
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set U_K : Set (EuclideanSpace ℝ (Fin d)) := Metric.cthickening δ K with hU_K_def
  have hU_K_compact : IsCompact U_K := hK_compact.cthickening
  have hU_K_closed : IsClosed U_K := Metric.isClosed_cthickening
  have hU_K_meas : MeasurableSet U_K := hU_K_closed.measurableSet
  have hK_in_U_K : K ⊆ U_K := Metric.self_subset_cthickening _
  have hU_K_in_Ω' : U_K ⊆ Ω' := hδ_in_Ω'
  have hU_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω'.trans hΩ'_in_Ω
  have h_eta_u_ae_eq_u : (fun x => η x * u x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω] u := by
    have h_eq_on_U_K : (fun x => η x * u x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict U_K] u := by
      refine (ae_restrict_iff' hU_K_meas).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx_eta : η x = 1 := hη_one_on_cthick x hx
      change η x * u x = u x
      rw [hx_eta]; ring
    have h_diff_meas : MeasurableSet (Ω \ U_K) := hΩ_meas.diff hU_K_meas
    have h_K_in_U_K : Ω \ U_K ⊆ Ω \ K := by
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hK_in_U_K hxK)⟩
    have hu_ae_zero_diff : ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ U_K)),
        u y = 0 := by
      have h_abs : (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ U_K) ≪
          (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_K_in_U_K le_rfl)
      exact h_abs.ae_le hu_ae_zero
    have h_eq_on_diff : (fun x => η x * u x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ U_K)] u := by
      filter_upwards [hu_ae_zero_diff] with x hx
      rw [hx]; ring
    have h_cover : Ω = U_K ∪ (Ω \ U_K) := by
      ext x; constructor
      · intro hx
        by_cases h : x ∈ U_K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hU_K_in_Ω hx
        · exact hx.1
    have hΩ_restrict_eq : (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω =
        (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  exact (Sobolev.Euclidean.MemWkp_congr_ae
    (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

end CalabiYau.PoissonDomainRegularity
