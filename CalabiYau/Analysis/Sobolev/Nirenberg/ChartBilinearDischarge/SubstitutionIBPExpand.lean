-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/ChartBilinearDischarge/SubstitutionIBPExpand.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionSmoothApprox

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeIBPExpand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open Sobolev.NirenbergTestFunction
open Sobolev.SubstitutionDischargeSmoothApprox
open Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem variational_identity_at_v_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (hv_h_lp : MemLp (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η D.uChart) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (hv_h_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (weak_partial_v_h j) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (uSeq : ℕ → EuclN → ℝ)
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n))
    (h_v_seq_support : ∀ n,
      tsupport (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η (uSeq n)) ⊆ Metric.cthickening |h| K_0)
    (h_v_seq_l2 :
      Tendsto (fun n => eLpNorm (fun x =>
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n) x -
        nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0))
    (h_v_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ
          (nirenbergTestFunction (d := Module.finrank ℝ E) k h η
            (uSeq n)) x) (EuclideanSpace.single j 1) -
          weak_partial_v_h j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0)) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              weak_partial_v_h j y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  set v_h : EuclN → ℝ := nirenbergTestFunction (d := Module.finrank ℝ E)
    k h η D.uChart with hvh_def
  set v_h_seq : ℕ → EuclN → ℝ := fun n =>
    nirenbergTestFunction (d := Module.finrank ℝ E) k h η (uSeq n)
    with hvhseq_def
  have h_v_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v_h_seq n) := fun n =>
    (nirenbergTestFunction_smooth_seq hη hη_support k hh hu_seq_smooth n).1
  have h_v_seq_cs : ∀ n, HasCompactSupport (v_h_seq n) := fun n =>
    (nirenbergTestFunction_smooth_seq hη hη_support k hh hu_seq_smooth n).2
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick v_h weak_partial_v_h hv_h_lp hv_h_grad_lp
    v_h_seq h_v_seq_smooth h_v_seq_cs h_v_seq_support h_v_seq_l2
    h_v_seq_grad_l2

theorem variational_identity_after_ibp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (h_expanded :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.uChart z) y)
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.fChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(volume : Measure EuclN))
    (h_ibp_per_ij : ∀ i j : Fin (Module.finrank ℝ E),
      ∫ y in Metric.cthickening |h| K_0,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y
        ∂(volume : Measure EuclN) =
      - ∫ y in Metric.cthickening |h| K_0,
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weakPartial i z) y *
          ((η y) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y)
        ∂(volume : Measure EuclN))
    (h_principal_integrable : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y)
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (h_principal_integrable_after : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y))
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) :
    -(∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weakPartial i z) y *
            ((η y) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart y))
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN) := by
  classical
  have h_int_swap_before :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.uChart z) y)
          ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y
            ∂(volume : Measure EuclN) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      intro j _
      exact h_principal_integrable i j
    · intro i _
      exact integrable_finsetSum _ (fun j _ => h_principal_integrable i j)
  have h_int_swap_after :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weakPartial i z) y *
            ((η y) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart y)
            ∂(volume : Measure EuclN) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      intro j _
      exact h_principal_integrable_after i j
    · intro i _
      exact integrable_finsetSum _ (fun j _ => h_principal_integrable_after i j)
  have h_per_ij_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.uChart z) y
            ∂(volume : Measure EuclN)) =
      - ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Metric.cthickening |h| K_0,
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y)
              ∂(volume : Measure EuclN) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h_ibp_per_ij i j
  rw [h_int_swap_before, h_per_ij_eq, ← h_int_swap_after] at h_expanded
  exact h_expanded

theorem variational_identity_after_product_rule
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (h_after_ibp :
      -(∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.fChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
          ∂(volume : Measure EuclN))
    (h_principal_in_K_0_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weakPartial i z) y *
              ((η y) ^ 2 *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.uChart y))
          ∂(volume : Measure EuclN) =
      principalTermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
        + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h)
    (h_c_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
      ∂(volume : Measure EuclN) =
      cTermChartBilinear (I := I) (M := M) D K_0 η k h)
    (h_f_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
      ∂(volume : Measure EuclN) =
      fTermChartBilinear (I := I) (M := M) D K_0 η k h) :
    principalTermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h
      + fTermChartBilinear (I := I) (M := M) D K_0 η k h
      = cTermChartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  rw [h_principal_in_K_0_eq, h_c_term_eq, h_f_term_eq] at h_after_ibp
  linarith

end SubstitutionDischargeIBPExpand
end Sobolev
end Analysis
end CalabiYau
